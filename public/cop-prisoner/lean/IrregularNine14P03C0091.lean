import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0034
import IrregularNine14P03C0035

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5460 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 25 208 169 233 169 425), lower := (rows 289 7 70 25 208 32 64 128 256), losses := [] }

theorem u5460 : Upper (D 3) (R 3) [288,5,66,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5460
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5461 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 41 145 248 216 216 472), lower := (rows 289 7 70 41 145 32 64 128 256), losses := [] }

theorem u5461 : Upper (D 3) (R 3) [288,5,66,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5461
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5462 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 41 152 241 209 209 465), lower := (rows 289 7 70 41 152 32 64 128 256), losses := [] }

theorem u5462 : Upper (D 3) (R 3) [288,5,66,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5462
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5463 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 56 81 169 201 137 393), lower := (rows 289 7 70 56 81 32 64 128 256), losses := [] }

theorem u5463 : Upper (D 3) (R 3) [288,5,66,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5463
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5464 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 56 88 161 193 129 385), lower := (rows 289 7 70 56 88 32 64 128 256), losses := [] }

theorem u5464 : Upper (D 3) (R 3) [288,5,66,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5464
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5465 : Route 9 := (fun mask => (mask,id))

def c5465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5465 : Upper (D 3) (R 3) [288,5,66,48,129] 13 := by
  apply FastRouting.sound _ _ [288,5,66,48,129] 13 (by decide) (choices 1) [1,8,64,128] r5465 c5465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2090
  · exact u2091
  · exact u2092
  · exact u2093

def b5466 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 56 152 225 193 193 449), lower := (rows 289 7 70 56 152 32 64 128 256), losses := [] }

theorem u5466 : Upper (D 3) (R 3) [288,5,66,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5467 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 56 208 169 201 137 393), lower := (rows 289 7 70 56 208 32 64 128 256), losses := [] }

theorem u5467 : Upper (D 3) (R 3) [288,5,66,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5467
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5468 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 145 184 248 184 440), lower := (rows 289 7 70 73 145 32 64 128 256), losses := [] }

theorem u5468 : Upper (D 3) (R 3) [288,5,66,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5468
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5469 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 152 177 241 177 433), lower := (rows 289 7 70 73 152 32 64 128 256), losses := [] }

theorem u5469 : Upper (D 3) (R 3) [288,5,66,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5469
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5470 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 176 185 217 153 409), lower := (rows 289 7 70 73 176 32 64 128 256), losses := [] }

theorem u5470 : Upper (D 3) (R 3) [288,5,66,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5470
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5471 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 145 169 233 169 425), lower := (rows 289 7 70 88 145 32 64 128 256), losses := [] }

theorem u5471 : Upper (D 3) (R 3) [288,5,66,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5471
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5472 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 152 161 225 161 417), lower := (rows 289 7 70 88 152 32 64 128 256), losses := [] }

theorem u5472 : Upper (D 3) (R 3) [288,5,66,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5472
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5473 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 176 169 201 137 393), lower := (rows 289 7 70 88 176 32 64 128 256), losses := [] }

theorem u5473 : Upper (D 3) (R 3) [288,5,66,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5473
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5474 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 145 185 217 153 409), lower := (rows 289 7 70 104 145 32 64 128 256), losses := [] }

theorem u5474 : Upper (D 3) (R 3) [288,5,66,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5474
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5475 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 152 177 209 145 401), lower := (rows 289 7 70 104 152 32 64 128 256), losses := [] }

theorem u5475 : Upper (D 3) (R 3) [288,5,66,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5475
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5476 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 70 137 145 120 120 248 376), lower := (rows 289 7 70 137 145 32 64 128 256), losses := [] }

theorem u5476 : Upper (D 3) (R 3) [288,5,66,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5476
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5477 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 70 137 152 113 113 241 369), lower := (rows 289 7 70 137 152 32 64 128 256), losses := [] }

theorem u5477 : Upper (D 3) (R 3) [288,5,66,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5477
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5478 : Route 9 := (fun mask => (mask,id))

def c5478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5478 : Upper (D 3) (R 3) [288,5,66,129,160] 13 := by
  apply FastRouting.sound _ _ [288,5,66,129,160] 13 (by decide) (choices 1) [1,8,16,64] r5478 c5478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2094
  · exact u2095
  · exact u2096
  · exact u2097

def b5479 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 137 208 57 121 185 313), lower := (rows 289 7 70 137 208 32 64 128 256), losses := [] }

theorem u5479 : Upper (D 3) (R 3) [288,5,66,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5479
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5480 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 70 152 152 97 97 225 353), lower := (rows 289 7 70 152 152 32 64 128 256), losses := [] }

theorem u5480 : Upper (D 3) (R 3) [288,5,66,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5480
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5481 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 70 152 176 105 73 201 329), lower := (rows 289 7 70 152 176 32 64 128 256), losses := [] }

theorem u5481 : Upper (D 3) (R 3) [288,5,66,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5481
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5482 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 70 152 208 41 105 169 297), lower := (rows 289 7 70 152 208 32 64 128 256), losses := [] }

theorem u5482 : Upper (D 3) (R 3) [288,5,66,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5482
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5483 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 168 208 57 89 153 281), lower := (rows 289 7 70 168 208 32 64 128 256), losses := [] }

theorem u5483 : Upper (D 3) (R 3) [288,5,66,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5483
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5484 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 82 161 225 161 417), lower := (rows 289 7 76 25 82 32 64 128 256), losses := [] }

theorem u5484 : Upper (D 3) (R 3) [288,5,72,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5484
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5485 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 112 163 195 131 387), lower := (rows 289 7 76 25 112 32 64 128 256), losses := [] }

theorem u5485 : Upper (D 3) (R 3) [288,5,72,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5485
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5486_128 : Upper (D 3) (R 3) [288,5,72,17,130,128] 13 :=
  permutation_upper _ _ _ [288,5,72,17,130,64] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2099

def r5486 : Route 9 := (fun mask => (mask,id))

def c5486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5486 : Upper (D 3) (R 3) [288,5,72,17,130] 13 := by
  apply FastRouting.sound _ _ [288,5,72,17,130] 13 (by decide) (choices 1) [1,64,128] r5486 c5486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2098
  · exact u2099
  · exact m5486_128

def b5487 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 25 176 227 195 195 451), lower := (rows 289 7 76 25 176 32 64 128 256), losses := [] }

theorem u5487 : Upper (D 3) (R 3) [288,5,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5487
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5488 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 208 163 227 163 419), lower := (rows 289 7 76 25 208 32 64 128 256), losses := [] }

theorem u5488 : Upper (D 3) (R 3) [288,5,72,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5488
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5489 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 26 49 225 193 193 449), lower := (rows 289 7 76 26 49 32 64 128 256), losses := [] }

theorem u5489 : Upper (D 3) (R 3) [288,5,72,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5489
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5490 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 26 81 161 225 161 417), lower := (rows 289 7 76 26 81 32 64 128 256), losses := [] }

theorem u5490 : Upper (D 3) (R 3) [288,5,72,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5490
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5491 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 112 161 193 129 385), lower := (rows 289 7 76 26 112 32 64 128 256), losses := [] }

theorem u5491 : Upper (D 3) (R 3) [288,5,72,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5492 : Route 9 := (fun mask => (mask,id))

def c5492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5492 : Upper (D 3) (R 3) [288,5,72,18,129] 13 := by
  apply FastRouting.sound _ _ [288,5,72,18,129] 13 (by decide) (choices 1) [1,64,128] r5492 c5492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2100
  · exact u2101
  · exact u2102

def b5493 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 289 7 76 26 176 225 193 193 449), lower := (rows 289 7 76 26 176 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 449 455 76 478 144 0 64 128 256) }] }

theorem u5493 : Upper (D 3) (R 3) [288,5,72,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5493
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5494 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 26 208 161 225 161 417), lower := (rows 289 7 76 26 208 32 64 128 256), losses := [] }

theorem u5494 : Upper (D 3) (R 3) [288,5,72,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5494
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5495 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 41 81 178 210 146 402), lower := (rows 289 7 76 41 81 32 64 128 256), losses := [] }

theorem u5495 : Upper (D 3) (R 3) [288,5,72,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5495
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5496 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 41 145 242 210 210 466), lower := (rows 289 7 76 41 145 32 64 128 256), losses := [] }

theorem u5496 : Upper (D 3) (R 3) [288,5,72,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5496
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5497 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 41 146 241 209 209 465), lower := (rows 289 7 76 41 146 32 64 128 256), losses := [] }

theorem u5497 : Upper (D 3) (R 3) [288,5,72,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5497
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5498 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 41 208 179 211 147 403), lower := (rows 289 7 76 41 208 32 64 128 256), losses := [] }

theorem u5498 : Upper (D 3) (R 3) [288,5,72,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5498
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5499 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 42 81 177 209 145 401), lower := (rows 289 7 76 42 81 32 64 128 256), losses := [] }

theorem u5499 : Upper (D 3) (R 3) [288,5,72,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5499
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5500 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 42 145 241 209 209 465), lower := (rows 289 7 76 42 145 32 64 128 256), losses := [] }

theorem u5500 : Upper (D 3) (R 3) [288,5,72,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5501 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 42 208 177 209 145 401), lower := (rows 289 7 76 42 208 32 64 128 256), losses := [] }

theorem u5501 : Upper (D 3) (R 3) [288,5,72,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5501
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5502 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 81 163 195 131 387), lower := (rows 289 7 76 56 81 32 64 128 256), losses := [] }

theorem u5502 : Upper (D 3) (R 3) [288,5,72,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5502
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5503 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 82 161 193 129 385), lower := (rows 289 7 76 56 82 32 64 128 256), losses := [] }

theorem u5503 : Upper (D 3) (R 3) [288,5,72,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5503
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5504 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 56 145 227 195 195 451), lower := (rows 289 7 76 56 145 32 64 128 256), losses := [] }

theorem u5504 : Upper (D 3) (R 3) [288,5,72,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5504
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5505 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 56 146 225 193 193 449), lower := (rows 289 7 76 56 146 32 64 128 256), losses := [] }

theorem u5505 : Upper (D 3) (R 3) [288,5,72,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5505
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5506 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 56 208 163 195 131 387), lower := (rows 289 7 76 56 208 32 64 128 256), losses := [] }

theorem u5506 : Upper (D 3) (R 3) [288,5,72,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5506
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5507 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 50 177 209 145 401), lower := (rows 289 7 76 73 50 32 64 128 256), losses := [] }

theorem u5507 : Upper (D 3) (R 3) [288,5,72,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5508 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 145 178 242 178 434), lower := (rows 289 7 76 73 145 32 64 128 256), losses := [] }

theorem u5508 : Upper (D 3) (R 3) [288,5,72,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5508
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5509 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 146 177 241 177 433), lower := (rows 289 7 76 73 146 32 64 128 256), losses := [] }

theorem u5509 : Upper (D 3) (R 3) [288,5,72,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5509
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5510 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 176 179 211 147 403), lower := (rows 289 7 76 73 176 32 64 128 256), losses := [] }

theorem u5510 : Upper (D 3) (R 3) [288,5,72,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5511 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 74 145 177 241 177 433), lower := (rows 289 7 76 74 145 32 64 128 256), losses := [] }

theorem u5511 : Upper (D 3) (R 3) [288,5,72,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5512 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 74 176 177 209 145 401), lower := (rows 289 7 76 74 176 32 64 128 256), losses := [] }

theorem u5512 : Upper (D 3) (R 3) [288,5,72,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5513 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 50 161 193 129 385), lower := (rows 289 7 76 88 50 32 64 128 256), losses := [] }

theorem u5513 : Upper (D 3) (R 3) [288,5,72,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5514 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 145 163 227 163 419), lower := (rows 289 7 76 88 145 32 64 128 256), losses := [] }

theorem u5514 : Upper (D 3) (R 3) [288,5,72,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5515 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 146 161 225 161 417), lower := (rows 289 7 76 88 146 32 64 128 256), losses := [] }

theorem u5515 : Upper (D 3) (R 3) [288,5,72,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5516 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 176 163 195 131 387), lower := (rows 289 7 76 88 176 32 64 128 256), losses := [] }

theorem u5516 : Upper (D 3) (R 3) [288,5,72,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5517 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 145 179 211 147 403), lower := (rows 289 7 76 104 145 32 64 128 256), losses := [] }

theorem u5517 : Upper (D 3) (R 3) [288,5,72,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5517
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5518 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 146 177 209 145 401), lower := (rows 289 7 76 104 146 32 64 128 256), losses := [] }

theorem u5518 : Upper (D 3) (R 3) [288,5,72,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5518
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5519 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 137 49 242 210 210 466), lower := (rows 289 7 76 137 49 32 64 128 256), losses := [] }

theorem u5519 : Upper (D 3) (R 3) [288,5,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5519
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5519
end Delivery.IrregularNine14.P03
