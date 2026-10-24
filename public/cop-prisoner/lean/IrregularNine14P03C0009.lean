import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0001

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b540 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 152 304 96 193 129 385), lower := (rows 7 35 76 152 304 96 64 128 256), losses := [] }

theorem u540 : Upper (D 3) (R 3) [6,33,72,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b540
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 152 304 160 65 193 321), lower := (rows 7 35 76 152 304 160 64 128 256), losses := [] }

theorem u541 : Upper (D 3) (R 3) [6,33,72,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 265 112 33 208 144 400), lower := (rows 7 35 76 265 112 33 64 128 256), losses := [] }

theorem u542 : Upper (D 3) (R 3) [6,33,72,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 76 265 112 48 193 129 385), lower := (rows 7 35 76 265 112 48 64 128 256), losses := [] }

theorem u543 : Upper (D 3) (R 3) [6,33,72,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r544 : Route 9 := (fun mask => (mask,id))

def c544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u544 : Upper (D 3) (R 3) [6,33,72,257,96,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,96,128] 13 (by decide) (choices 1) [1,16,128] r544 c544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u63
  · exact u64
  · exact u65

def b545 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 7 35 76 265 145 48 224 224 480), lower := (rows 7 35 76 265 145 48 64 128 256), losses := [] }

theorem u545 : Upper (D 3) (R 3) [6,33,72,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 265 145 96 240 176 432), lower := (rows 7 35 76 265 145 96 64 128 256), losses := [] }

theorem u546 : Upper (D 3) (R 3) [6,33,72,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 76 265 145 160 112 240 368), lower := (rows 7 35 76 265 145 160 64 128 256), losses := [] }

theorem u547 : Upper (D 3) (R 3) [6,33,72,257,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 265 176 33 208 208 464), lower := (rows 7 35 76 265 176 33 64 128 256), losses := [] }

theorem u548 : Upper (D 3) (R 3) [6,33,72,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b548
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 76 265 176 48 193 193 449), lower := (rows 7 35 76 265 176 48 64 128 256), losses := [] }

theorem u549 : Upper (D 3) (R 3) [6,33,72,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 265 176 96 209 145 401), lower := (rows 7 35 76 265 176 96 64 128 256), losses := [] }

theorem u550 : Upper (D 3) (R 3) [6,33,72,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b550
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 265 176 160 81 209 337), lower := (rows 7 35 76 265 176 160 64 128 256), losses := [] }

theorem u551 : Upper (D 3) (R 3) [6,33,72,257,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 265 208 33 240 176 432), lower := (rows 7 35 76 265 208 33 64 128 256), losses := [] }

theorem u552 : Upper (D 3) (R 3) [6,33,72,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b552
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 76 265 208 48 225 161 417), lower := (rows 7 35 76 265 208 48 64 128 256), losses := [] }

theorem u553 : Upper (D 3) (R 3) [6,33,72,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r554 : Route 9 := (fun mask => (mask,id))

def c554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u554 : Upper (D 3) (R 3) [6,33,72,257,192,128] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,192,128] 13 (by decide) (choices 1) [1,16,32] r554 c554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u66
  · exact u67
  · exact u68

def b555 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 145 33 224 224 480), lower := (rows 7 35 76 280 145 33 64 128 256), losses := [] }

theorem u555 : Upper (D 3) (R 3) [6,33,72,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 280 145 96 225 161 417), lower := (rows 7 35 76 280 145 96 64 128 256), losses := [] }

theorem u556 : Upper (D 3) (R 3) [6,33,72,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 76 280 145 160 97 225 353), lower := (rows 7 35 76 280 145 160 64 128 256), losses := [] }

theorem u557 : Upper (D 3) (R 3) [6,33,72,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b557
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 176 33 193 193 449), lower := (rows 7 35 76 280 176 33 64 128 256), losses := [] }

theorem u558 : Upper (D 3) (R 3) [6,33,72,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b558
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 280 176 96 193 129 385), lower := (rows 7 35 76 280 176 96 64 128 256), losses := [] }

theorem u559 : Upper (D 3) (R 3) [6,33,72,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b559
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 280 176 160 65 193 321), lower := (rows 7 35 76 280 176 160 64 128 256), losses := [] }

theorem u560 : Upper (D 3) (R 3) [6,33,72,272,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b560
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 392 112 33 209 145 401), lower := (rows 7 35 76 392 112 33 64 128 256), losses := [] }

theorem u561 : Upper (D 3) (R 3) [6,33,72,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 76 392 112 48 193 129 385), lower := (rows 7 35 76 392 112 48 64 128 256), losses := [] }

theorem u562 : Upper (D 3) (R 3) [6,33,72,384,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b562
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 7 35 76 392 112 160 81 145 273), lower := (rows 7 35 76 392 112 160 64 128 256), losses := [] }

theorem u563 : Upper (D 3) (R 3) [6,33,72,384,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 392 176 33 81 209 337), lower := (rows 7 35 76 392 176 33 64 128 256), losses := [] }

theorem u564 : Upper (D 3) (R 3) [6,33,72,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b564
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 35 76 392 176 48 65 193 321), lower := (rows 7 35 76 392 176 48 64 128 256), losses := [] }

theorem u565 : Upper (D 3) (R 3) [6,33,72,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b565
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 392 176 96 81 145 273), lower := (rows 7 35 76 392 176 96 64 128 256), losses := [] }

theorem u566 : Upper (D 3) (R 3) [6,33,72,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 392 208 33 113 177 305), lower := (rows 7 35 76 392 208 33 64 128 256), losses := [] }

theorem u567 : Upper (D 3) (R 3) [6,33,72,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 76 392 208 48 97 161 289), lower := (rows 7 35 76 392 208 48 64 128 256), losses := [] }

theorem u568 : Upper (D 3) (R 3) [6,33,72,384,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b568
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 25 280 33 224 224 480), lower := (rows 7 35 196 25 280 33 64 128 256), losses := [] }

theorem u569 : Upper (D 3) (R 3) [6,33,192,17,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b569
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 25 280 96 225 161 417), lower := (rows 7 35 196 25 280 96 64 128 256), losses := [] }

theorem u570 : Upper (D 3) (R 3) [6,33,192,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b570
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 56 273 33 200 200 456), lower := (rows 7 35 196 56 273 33 64 128 256), losses := [] }

theorem u571 : Upper (D 3) (R 3) [6,33,192,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 196 56 273 40 193 193 449), lower := (rows 7 35 196 56 273 40 64 128 256), losses := [] }

theorem u572 : Upper (D 3) (R 3) [6,33,192,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b572
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 56 273 96 201 137 393), lower := (rows 7 35 196 56 273 96 64 128 256), losses := [] }

theorem u573 : Upper (D 3) (R 3) [6,33,192,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b573
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 56 336 33 201 137 393), lower := (rows 7 35 196 56 336 33 64 128 256), losses := [] }

theorem u574 : Upper (D 3) (R 3) [6,33,192,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b574
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 196 56 336 40 193 129 385), lower := (rows 7 35 196 56 336 40 64 128 256), losses := [] }

theorem u575 : Upper (D 3) (R 3) [6,33,192,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b575
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 56 336 160 73 137 265), lower := (rows 7 35 196 56 336 160 64 128 256), losses := [] }

theorem u576 : Upper (D 3) (R 3) [6,33,192,48,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 176 33 329 393 265), lower := (rows 7 35 196 88 176 33 64 128 256), losses := [] }

theorem u577 : Upper (D 3) (R 3) [6,33,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 7 35 196 88 176 40 321 385 257), lower := (rows 7 35 196 88 176 40 64 128 256), losses := [] }

theorem u578 : Upper (D 3) (R 3) [6,33,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b578
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 35 196 88 176 288 73 137 265), lower := (rows 7 35 196 88 176 288 64 128 256), losses := [] }

theorem u579 : Upper (D 3) (R 3) [6,33,192,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b579
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 273 33 232 168 424), lower := (rows 7 35 196 88 273 33 64 128 256), losses := [] }

theorem u580 : Upper (D 3) (R 3) [6,33,192,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 35 196 88 273 40 225 161 417), lower := (rows 7 35 196 88 273 40 64 128 256), losses := [] }

theorem u581 : Upper (D 3) (R 3) [6,33,192,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b581
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 88 273 160 105 169 297), lower := (rows 7 35 196 88 273 160 64 128 256), losses := [] }

theorem u582 : Upper (D 3) (R 3) [6,33,192,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 304 33 201 137 393), lower := (rows 7 35 196 88 304 33 64 128 256), losses := [] }

theorem u583 : Upper (D 3) (R 3) [6,33,192,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b583
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 196 88 304 40 193 129 385), lower := (rows 7 35 196 88 304 40 64 128 256), losses := [] }

theorem u584 : Upper (D 3) (R 3) [6,33,192,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b584
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 88 304 160 73 137 265), lower := (rows 7 35 196 88 304 160 64 128 256), losses := [] }

theorem u585 : Upper (D 3) (R 3) [6,33,192,80,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b585
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 400 33 105 169 297), lower := (rows 7 35 196 88 400 33 64 128 256), losses := [] }

theorem u586 : Upper (D 3) (R 3) [6,33,192,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b586
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 196 88 400 40 97 161 289), lower := (rows 7 35 196 88 400 40 64 128 256), losses := [] }

theorem u587 : Upper (D 3) (R 3) [6,33,192,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b587
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 196 104 273 33 216 152 408), lower := (rows 7 35 196 104 273 33 64 128 256), losses := [] }

theorem u588 : Upper (D 3) (R 3) [6,33,192,96,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b588
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 35 196 104 273 40 209 145 401), lower := (rows 7 35 196 104 273 40 64 128 256), losses := [] }

theorem u589 : Upper (D 3) (R 3) [6,33,192,96,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b589
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 35 196 104 273 48 201 137 393), lower := (rows 7 35 196 104 273 48 64 128 256), losses := [] }

theorem u590 : Upper (D 3) (R 3) [6,33,192,96,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 104 273 160 89 153 281), lower := (rows 7 35 196 104 273 160 64 128 256), losses := [] }

theorem u591 : Upper (D 3) (R 3) [6,33,192,96,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 196 104 280 33 209 145 401), lower := (rows 7 35 196 104 280 33 64 128 256), losses := [] }

theorem u592 : Upper (D 3) (R 3) [6,33,192,96,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b592
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 196 104 280 48 193 129 385), lower := (rows 7 35 196 104 280 48 64 128 256), losses := [] }

theorem u593 : Upper (D 3) (R 3) [6,33,192,96,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b593
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 7 35 196 104 280 160 81 145 273), lower := (rows 7 35 196 104 280 160 64 128 256), losses := [] }

theorem u594 : Upper (D 3) (R 3) [6,33,192,96,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 196 104 400 33 89 153 281), lower := (rows 7 35 196 104 400 33 64 128 256), losses := [] }

theorem u595 : Upper (D 3) (R 3) [6,33,192,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 35 196 104 400 40 81 145 273), lower := (rows 7 35 196 104 400 40 64 128 256), losses := [] }

theorem u596 : Upper (D 3) (R 3) [6,33,192,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b596
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 35 196 104 400 48 73 137 265), lower := (rows 7 35 196 104 400 48 64 128 256), losses := [] }

theorem u597 : Upper (D 3) (R 3) [6,33,192,96,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b597
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 56 208 33 200 200 456), lower := (rows 7 35 261 56 208 33 64 128 256), losses := [] }

theorem u598 : Upper (D 3) (R 3) [6,33,257,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b598
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 35 261 56 208 40 193 193 449), lower := (rows 7 35 261 56 208 40 64 128 256), losses := [] }

theorem u599 : Upper (D 3) (R 3) [6,33,257,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b599
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P03
