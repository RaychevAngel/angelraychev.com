import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0035

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5520 : Route 9 := (fun mask => (mask,id))

def c5520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5520 : Upper (D 3) (R 3) [288,5,72,129,34] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,34] 13 (by decide) (choices 1) [1,16,64,128] r5520 c5520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2103
  · exact u2104
  · exact u2105
  · exact u2106

def r5521 : Route 9 := (fun mask => (mask,id))

def c5521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5521 : Upper (D 3) (R 3) [288,5,72,129,65] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,65] 13 (by decide) (choices 1) [2,16,128] r5521 c5521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2107
  · exact u2108
  · exact u2109

def b5522 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 137 82 177 241 177 433), lower := (rows 289 7 76 137 82 32 64 128 256), losses := [] }

theorem u5522 : Upper (D 3) (R 3) [288,5,72,129,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5523 : Route 9 := (fun mask => (mask,id))

def c5523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5523 : Upper (D 3) (R 3) [288,5,72,129,96] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,96] 13 (by decide) (choices 1) [1,2,16,128] r5523 c5523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2110
  · exact u2111
  · exact u2112
  · exact u2113

def b5524 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 137 145 114 114 242 370), lower := (rows 289 7 76 137 145 32 64 128 256), losses := [] }

theorem u5524 : Upper (D 3) (R 3) [288,5,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5524
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 137 146 113 113 241 369), lower := (rows 289 7 76 137 146 32 64 128 256), losses := [] }

theorem u5525 : Upper (D 3) (R 3) [288,5,72,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5525
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5526 : Route 9 := (fun mask => (mask,id))

def c5526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5526 : Upper (D 3) (R 3) [288,5,72,129,160] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,160] 13 (by decide) (choices 1) [1,2,16,64] r5526 c5526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2114
  · exact u2115
  · exact u2116
  · exact u2117

def r5527 : Route 9 := (fun mask => (mask,id))

def c5527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5527 : Upper (D 3) (R 3) [288,5,72,129,192] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129,192] 13 (by decide) (choices 1) [1,2,16] r5527 c5527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2118
  · exact u2119
  · exact u2120

def b5528 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 138 49 241 209 209 465), lower := (rows 289 7 76 138 49 32 64 128 256), losses := [] }

theorem u5528 : Upper (D 3) (R 3) [288,5,72,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5528
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5529 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 138 81 177 241 177 433), lower := (rows 289 7 76 138 81 32 64 128 256), losses := [] }

theorem u5529 : Upper (D 3) (R 3) [288,5,72,130,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5530 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 138 112 177 209 145 401), lower := (rows 289 7 76 138 112 32 64 128 256), losses := [] }

theorem u5530 : Upper (D 3) (R 3) [288,5,72,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5531 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 138 145 113 113 241 369), lower := (rows 289 7 76 138 145 32 64 128 256), losses := [] }

theorem u5531 : Upper (D 3) (R 3) [288,5,72,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5531
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5532 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 138 176 113 81 209 337), lower := (rows 289 7 76 138 176 32 64 128 256), losses := [] }

theorem u5532 : Upper (D 3) (R 3) [288,5,72,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5532
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5533 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 138 208 49 113 177 305), lower := (rows 289 7 76 138 208 32 64 128 256), losses := [] }

theorem u5533 : Upper (D 3) (R 3) [288,5,72,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5533
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5534 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 152 49 227 195 195 451), lower := (rows 289 7 76 152 49 32 64 128 256), losses := [] }

theorem u5534 : Upper (D 3) (R 3) [288,5,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5534
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5535 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 289 7 76 152 50 225 193 193 449), lower := (rows 289 7 76 152 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 449 455 76 156 478 0 64 128 256) }] }

theorem u5535 : Upper (D 3) (R 3) [288,5,72,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5535
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5536 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 81 163 227 163 419), lower := (rows 289 7 76 152 81 32 64 128 256), losses := [] }

theorem u5536 : Upper (D 3) (R 3) [288,5,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5536
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5537 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 82 161 225 161 417), lower := (rows 289 7 76 152 82 32 64 128 256), losses := [] }

theorem u5537 : Upper (D 3) (R 3) [288,5,72,144,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5538 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 152 112 163 195 131 387), lower := (rows 289 7 76 152 112 32 64 128 256), losses := [] }

theorem u5538 : Upper (D 3) (R 3) [288,5,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5538
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5539 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 145 99 99 227 355), lower := (rows 289 7 76 152 145 32 64 128 256), losses := [] }

theorem u5539 : Upper (D 3) (R 3) [288,5,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5539
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 146 97 97 225 353), lower := (rows 289 7 76 152 146 32 64 128 256), losses := [] }

theorem u5540 : Upper (D 3) (R 3) [288,5,72,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5540
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 76 152 176 99 67 195 323), lower := (rows 289 7 76 152 176 32 64 128 256), losses := [] }

theorem u5541 : Upper (D 3) (R 3) [288,5,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5542 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 76 152 208 35 99 163 291), lower := (rows 289 7 76 152 208 32 64 128 256), losses := [] }

theorem u5542 : Upper (D 3) (R 3) [288,5,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5543 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 168 81 179 211 147 403), lower := (rows 289 7 76 168 81 32 64 128 256), losses := [] }

theorem u5543 : Upper (D 3) (R 3) [288,5,72,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 168 82 177 209 145 401), lower := (rows 289 7 76 168 82 32 64 128 256), losses := [] }

theorem u5544 : Upper (D 3) (R 3) [288,5,72,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5544
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5545 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 168 145 115 83 211 339), lower := (rows 289 7 76 168 145 32 64 128 256), losses := [] }

theorem u5545 : Upper (D 3) (R 3) [288,5,72,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5546 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 168 146 113 81 209 337), lower := (rows 289 7 76 168 146 32 64 128 256), losses := [] }

theorem u5546 : Upper (D 3) (R 3) [288,5,72,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5547 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 168 208 51 83 147 275), lower := (rows 289 7 76 168 208 32 64 128 256), losses := [] }

theorem u5547 : Upper (D 3) (R 3) [288,5,72,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5548 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 50 177 209 145 401), lower := (rows 289 7 76 200 50 32 64 128 256), losses := [] }

theorem u5548 : Upper (D 3) (R 3) [288,5,72,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5548
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5549 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 145 51 115 179 307), lower := (rows 289 7 76 200 145 32 64 128 256), losses := [] }

theorem u5549 : Upper (D 3) (R 3) [288,5,72,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5550 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 146 49 113 177 305), lower := (rows 289 7 76 200 146 32 64 128 256), losses := [] }

theorem u5550 : Upper (D 3) (R 3) [288,5,72,192,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5550
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5551 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 176 51 83 147 275), lower := (rows 289 7 76 200 176 32 64 128 256), losses := [] }

theorem u5551 : Upper (D 3) (R 3) [288,5,72,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5552 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 25 208 171 203 139 395), lower := (rows 289 7 100 25 208 32 64 128 256), losses := [] }

theorem u5552 : Upper (D 3) (R 3) [288,5,96,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5552
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5553 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 26 81 169 201 137 393), lower := (rows 289 7 100 26 81 32 64 128 256), losses := [] }

theorem u5553 : Upper (D 3) (R 3) [288,5,96,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 26 88 161 193 129 385), lower := (rows 289 7 100 26 88 32 64 128 256), losses := [] }

theorem u5554 : Upper (D 3) (R 3) [288,5,96,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5554
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 26 145 233 201 201 457), lower := (rows 289 7 100 26 145 32 64 128 256), losses := [] }

theorem u5555 : Upper (D 3) (R 3) [288,5,96,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 26 152 225 193 193 449), lower := (rows 289 7 100 26 152 32 64 128 256), losses := [] }

theorem u5556 : Upper (D 3) (R 3) [288,5,96,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 26 208 169 201 137 393), lower := (rows 289 7 100 26 208 32 64 128 256), losses := [] }

theorem u5557 : Upper (D 3) (R 3) [288,5,96,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5557
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5558 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 73 145 186 218 154 410), lower := (rows 289 7 100 73 145 32 64 128 256), losses := [] }

theorem u5558 : Upper (D 3) (R 3) [288,5,96,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5558
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5559 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 73 146 185 217 153 409), lower := (rows 289 7 100 73 146 32 64 128 256), losses := [] }

theorem u5559 : Upper (D 3) (R 3) [288,5,96,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5559
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5560 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 73 152 179 211 147 403), lower := (rows 289 7 100 73 152 32 64 128 256), losses := [] }

theorem u5560 : Upper (D 3) (R 3) [288,5,96,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5560
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5561 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 74 145 185 217 153 409), lower := (rows 289 7 100 74 145 32 64 128 256), losses := [] }

theorem u5561 : Upper (D 3) (R 3) [288,5,96,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5562 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 74 152 177 209 145 401), lower := (rows 289 7 100 74 152 32 64 128 256), losses := [] }

theorem u5562 : Upper (D 3) (R 3) [288,5,96,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5562
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5563 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 88 145 171 203 139 395), lower := (rows 289 7 100 88 145 32 64 128 256), losses := [] }

theorem u5563 : Upper (D 3) (R 3) [288,5,96,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5564 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 88 146 169 201 137 393), lower := (rows 289 7 100 88 146 32 64 128 256), losses := [] }

theorem u5564 : Upper (D 3) (R 3) [288,5,96,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5564
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5565 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 88 152 163 195 131 387), lower := (rows 289 7 100 88 152 32 64 128 256), losses := [] }

theorem u5565 : Upper (D 3) (R 3) [288,5,96,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5565
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5566 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 137 146 121 89 217 345), lower := (rows 289 7 100 137 146 32 64 128 256), losses := [] }

theorem u5566 : Upper (D 3) (R 3) [288,5,96,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 137 208 59 91 155 283), lower := (rows 289 7 100 137 208 32 64 128 256), losses := [] }

theorem u5567 : Upper (D 3) (R 3) [288,5,96,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 138 208 57 89 153 281), lower := (rows 289 7 100 138 208 32 64 128 256), losses := [] }

theorem u5568 : Upper (D 3) (R 3) [288,5,96,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5568
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5569 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 25 208 43 107 171 299), lower := (rows 289 7 196 25 208 32 64 128 256), losses := [] }

theorem u5569 : Upper (D 3) (R 3) [288,5,192,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5569
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5570 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 196 26 49 233 201 201 457), lower := (rows 289 7 196 26 49 32 64 128 256), losses := [] }

theorem u5570 : Upper (D 3) (R 3) [288,5,192,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5570
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 196 26 56 225 193 193 449), lower := (rows 289 7 196 26 56 32 64 128 256), losses := [] }

theorem u5571 : Upper (D 3) (R 3) [288,5,192,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5572 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 26 81 169 233 169 425), lower := (rows 289 7 196 26 81 32 64 128 256), losses := [] }

theorem u5572 : Upper (D 3) (R 3) [288,5,192,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5572
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5573 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 26 88 161 225 161 417), lower := (rows 289 7 196 26 88 32 64 128 256), losses := [] }

theorem u5573 : Upper (D 3) (R 3) [288,5,192,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5573
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 26 112 169 201 137 393), lower := (rows 289 7 196 26 112 32 64 128 256), losses := [] }

theorem u5574 : Upper (D 3) (R 3) [288,5,192,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5574
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 196 26 208 41 105 169 297), lower := (rows 289 7 196 26 208 32 64 128 256), losses := [] }

theorem u5575 : Upper (D 3) (R 3) [288,5,192,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5575
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 196 41 81 186 218 154 410), lower := (rows 289 7 196 41 81 32 64 128 256), losses := [] }

theorem u5576 : Upper (D 3) (R 3) [288,5,192,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 196 41 88 179 211 147 403), lower := (rows 289 7 196 41 88 32 64 128 256), losses := [] }

theorem u5577 : Upper (D 3) (R 3) [288,5,192,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5578 : Route 9 := (fun mask => (mask,id))

def c5578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5578 : Upper (D 3) (R 3) [288,5,192,34,65] 13 := by
  apply FastRouting.sound _ _ [288,5,192,34,65] 13 (by decide) (choices 1) [1,8,16,128] r5578 c5578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2121
  · exact u2122
  · exact u2123
  · exact u2124

def b5579 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 42 88 177 209 145 401), lower := (rows 289 7 196 42 88 32 64 128 256), losses := [] }

theorem u5579 : Upper (D 3) (R 3) [288,5,192,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5579
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5579
end Delivery.IrregularNine14.P03
