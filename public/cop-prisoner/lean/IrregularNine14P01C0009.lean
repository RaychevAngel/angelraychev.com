import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0000

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b540 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 392 48 160 82 210 338), lower := (rows 51 7 76 392 48 160 64 128 256), losses := [] }

theorem u540 : Upper (D 1) (R 1) [50,5,72,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 392 80 160 114 178 306), lower := (rows 51 7 76 392 80 160 64 128 256), losses := [] }

theorem u541 : Upper (D 1) (R 1) [50,5,72,384,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b541
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 88 144 34 224 224 480), lower := (rows 51 7 268 88 144 34 64 128 256), losses := [] }

theorem u542 : Upper (D 1) (R 1) [50,5,264,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b542
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r543 : Route 9 := (fun mask => (mask,id))

def c543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u543 : Upper (D 1) (R 1) [50,5,264,80,128,64] 13 := by
  apply FastRouting.sound _ _ [50,5,264,80,128,64] 13 (by decide) (choices 1) [2,32,128] r543 c543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u32
  · exact u33
  · exact u34

def b544 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 268 88 144 160 98 226 354), lower := (rows 51 7 268 88 144 160 64 128 256), losses := [] }

theorem u544 : Upper (D 1) (R 1) [50,5,264,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 200 18 96 240 176 432), lower := (rows 51 7 268 200 18 96 64 128 256), losses := [] }

theorem u545 : Upper (D 1) (R 1) [50,5,264,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 268 200 48 96 210 146 402), lower := (rows 51 7 268 200 48 96 64 128 256), losses := [] }

theorem u546 : Upper (D 1) (R 1) [50,5,264,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r547 : Route 9 := (fun mask => (mask,id))

def c547 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u547 : Upper (D 1) (R 1) [50,5,264,192,64,128] 13 := by
  apply FastRouting.sound _ _ [50,5,264,192,64,128] 13 (by decide) (choices 1) [2,16,32] r547 c547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u35
  · exact u36
  · exact u37

def b548 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 88 144 34 232 168 424), lower := (rows 51 7 324 88 144 34 64 128 256), losses := [] }

theorem u548 : Upper (D 1) (R 1) [50,5,320,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 7 324 88 144 40 226 162 418), lower := (rows 51 7 324 88 144 40 64 128 256), losses := [] }

theorem u549 : Upper (D 1) (R 1) [50,5,320,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b550 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 7 324 88 144 160 106 170 298), lower := (rows 51 7 324 88 144 160 64 128 256), losses := [] }

theorem u550 : Upper (D 1) (R 1) [50,5,320,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 200 18 160 120 184 312), lower := (rows 51 7 324 200 18 160 64 128 256), losses := [] }

theorem u551 : Upper (D 1) (R 1) [50,5,320,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b551
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 7 324 200 24 160 114 178 306), lower := (rows 51 7 324 200 24 160 64 128 256), losses := [] }

theorem u552 : Upper (D 1) (R 1) [50,5,320,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b552
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 200 48 160 90 154 282), lower := (rows 51 7 324 200 48 160 64 128 256), losses := [] }

theorem u553 : Upper (D 1) (R 1) [50,5,320,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 104 144 34 452 388 388), lower := (rows 51 67 28 104 144 34 64 128 256), losses := [] }

theorem u554 : Upper (D 1) (R 1) [50,65,24,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 386, camps := [], pairs := [], upper := (rows 51 67 28 104 144 36 450 386 386), lower := (rows 51 67 28 104 144 36 64 128 256), losses := [] }

theorem u555 : Upper (D 1) (R 1) [50,65,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b555
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 28 104 144 160 326 390 262), lower := (rows 51 67 28 104 144 160 64 128 256), losses := [] }

theorem u556 : Upper (D 1) (R 1) [50,65,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 67 28 104 144 288 198 134 390), lower := (rows 51 67 28 104 144 288 64 128 256), losses := [] }

theorem u557 : Upper (D 1) (R 1) [50,65,24,96,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 296 144 34 196 196 452), lower := (rows 51 67 28 296 144 34 64 128 256), losses := [] }

theorem u558 : Upper (D 1) (R 1) [50,65,24,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 51 67 28 296 144 36 194 194 450), lower := (rows 51 67 28 296 144 36 64 128 256), losses := [] }

theorem u559 : Upper (D 1) (R 1) [50,65,24,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b559
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 296 144 96 198 134 390), lower := (rows 51 67 28 296 144 96 64 128 256), losses := [] }

theorem u560 : Upper (D 1) (R 1) [50,65,24,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b560
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 28 296 144 160 70 198 326), lower := (rows 51 67 28 296 144 160 64 128 256), losses := [] }

theorem u561 : Upper (D 1) (R 1) [50,65,24,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 328 144 34 228 164 420), lower := (rows 51 67 28 328 144 34 64 128 256), losses := [] }

theorem u562 : Upper (D 1) (R 1) [50,65,24,320,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 67 28 328 144 36 226 162 418), lower := (rows 51 67 28 328 144 36 64 128 256), losses := [] }

theorem u563 : Upper (D 1) (R 1) [50,65,24,320,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 28 328 144 160 102 166 294), lower := (rows 51 67 28 328 144 160 64 128 256), losses := [] }

theorem u564 : Upper (D 1) (R 1) [50,65,24,320,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 280 144 34 228 164 420), lower := (rows 51 67 76 280 144 34 64 128 256), losses := [] }

theorem u565 : Upper (D 1) (R 1) [50,65,72,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b565
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 67 76 280 144 36 226 162 418), lower := (rows 51 67 76 280 144 36 64 128 256), losses := [] }

theorem u566 : Upper (D 1) (R 1) [50,65,72,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 76 280 144 160 102 166 294), lower := (rows 51 67 76 280 144 160 64 128 256), losses := [] }

theorem u567 : Upper (D 1) (R 1) [50,65,72,272,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 76 392 18 160 116 180 308), lower := (rows 51 67 76 392 18 160 64 128 256), losses := [] }

theorem u568 : Upper (D 1) (R 1) [50,65,72,384,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 67 76 392 20 160 114 178 306), lower := (rows 51 67 76 392 20 160 64 128 256), losses := [] }

theorem u569 : Upper (D 1) (R 1) [50,65,72,384,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 392 48 160 86 150 278), lower := (rows 51 67 76 392 48 160 64 128 256), losses := [] }

theorem u570 : Upper (D 1) (R 1) [50,65,72,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 140 144 34 360 424 296), lower := (rows 51 67 84 140 144 34 64 128 256), losses := [] }

theorem u571 : Upper (D 1) (R 1) [50,65,80,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 290, camps := [], pairs := [], upper := (rows 51 67 84 140 144 40 354 418 290), lower := (rows 51 67 84 140 144 40 64 128 256), losses := [] }

theorem u572 : Upper (D 1) (R 1) [50,65,80,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 51 67 84 140 144 288 106 170 298), lower := (rows 51 67 84 140 144 288 64 128 256), losses := [] }

theorem u573 : Upper (D 1) (R 1) [50,65,80,132,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b573
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 168 144 34 332 396 268), lower := (rows 51 67 84 168 144 34 64 128 256), losses := [] }

theorem u574 : Upper (D 1) (R 1) [50,65,80,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b574
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 266, camps := [], pairs := [], upper := (rows 51 67 84 168 144 36 330 394 266), lower := (rows 51 67 84 168 144 36 64 128 256), losses := [] }

theorem u575 : Upper (D 1) (R 1) [50,65,80,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b575
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 262, camps := [], pairs := [], upper := (rows 51 67 84 168 144 40 326 390 262), lower := (rows 51 67 84 168 144 40 64 128 256), losses := [] }

theorem u576 : Upper (D 1) (R 1) [50,65,80,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 51 67 84 168 144 288 78 142 270), lower := (rows 51 67 84 168 144 288 64 128 256), losses := [] }

theorem u577 : Upper (D 1) (R 1) [50,65,80,160,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 268 144 34 232 168 424), lower := (rows 51 67 84 268 144 34 64 128 256), losses := [] }

theorem u578 : Upper (D 1) (R 1) [50,65,80,260,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b578
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 67 84 268 144 40 226 162 418), lower := (rows 51 67 84 268 144 40 64 128 256), losses := [] }

theorem u579 : Upper (D 1) (R 1) [50,65,80,260,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b579
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 84 268 144 160 106 170 298), lower := (rows 51 67 84 268 144 160 64 128 256), losses := [] }

theorem u580 : Upper (D 1) (R 1) [50,65,80,260,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 296 144 34 204 140 396), lower := (rows 51 67 84 296 144 34 64 128 256), losses := [] }

theorem u581 : Upper (D 1) (R 1) [50,65,80,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 51 67 84 296 144 36 202 138 394), lower := (rows 51 67 84 296 144 36 64 128 256), losses := [] }

theorem u582 : Upper (D 1) (R 1) [50,65,80,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 67 84 296 144 40 198 134 390), lower := (rows 51 67 84 296 144 40 64 128 256), losses := [] }

theorem u583 : Upper (D 1) (R 1) [50,65,80,288,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 67 84 296 144 160 78 142 270), lower := (rows 51 67 84 296 144 160 64 128 256), losses := [] }

theorem u584 : Upper (D 1) (R 1) [50,65,80,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 84 392 144 34 108 172 300), lower := (rows 51 67 84 392 144 34 64 128 256), losses := [] }

theorem u585 : Upper (D 1) (R 1) [50,65,80,384,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 51 67 84 392 144 36 106 170 298), lower := (rows 51 67 84 392 144 36 64 128 256), losses := [] }

theorem u586 : Upper (D 1) (R 1) [50,65,80,384,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b586
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 51 67 84 392 144 40 102 166 294), lower := (rows 51 67 84 392 144 40 64 128 256), losses := [] }

theorem u587 : Upper (D 1) (R 1) [50,65,80,384,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b587
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 280 144 34 100 228 356), lower := (rows 51 67 140 280 144 34 64 128 256), losses := [] }

theorem u588 : Upper (D 1) (R 1) [50,65,136,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b588
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 51 67 140 280 144 36 98 226 354), lower := (rows 51 67 140 280 144 36 64 128 256), losses := [] }

theorem u589 : Upper (D 1) (R 1) [50,65,136,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 280 144 96 102 166 294), lower := (rows 51 67 140 280 144 96 64 128 256), losses := [] }

theorem u590 : Upper (D 1) (R 1) [50,65,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 140 328 18 160 116 180 308), lower := (rows 51 67 140 328 18 160 64 128 256), losses := [] }

theorem u591 : Upper (D 1) (R 1) [50,65,136,320,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 67 140 328 20 160 114 178 306), lower := (rows 51 67 140 328 20 160 64 128 256), losses := [] }

theorem u592 : Upper (D 1) (R 1) [50,65,136,320,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b592
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 328 48 160 86 150 278), lower := (rows 51 67 140 328 48 160 64 128 256), losses := [] }

theorem u593 : Upper (D 1) (R 1) [50,65,136,320,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 196 268 18 160 120 184 312), lower := (rows 51 67 196 268 18 160 64 128 256), losses := [] }

theorem u594 : Upper (D 1) (R 1) [50,65,192,260,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 51 67 196 268 24 160 114 178 306), lower := (rows 51 67 196 268 24 160 64 128 256), losses := [] }

theorem u595 : Upper (D 1) (R 1) [50,65,192,260,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 268 48 160 90 154 282), lower := (rows 51 67 196 268 48 160 64 128 256), losses := [] }

theorem u596 : Upper (D 1) (R 1) [50,65,192,260,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 196 280 144 34 108 172 300), lower := (rows 51 67 196 280 144 34 64 128 256), losses := [] }

theorem u597 : Upper (D 1) (R 1) [50,65,192,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b597
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 51 67 196 280 144 36 106 170 298), lower := (rows 51 67 196 280 144 36 64 128 256), losses := [] }

theorem u598 : Upper (D 1) (R 1) [50,65,192,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 38, camps := [], pairs := [], upper := (rows 51 67 196 280 144 40 102 166 294), lower := (rows 51 67 196 280 144 40 64 128 256), losses := [] }

theorem u599 : Upper (D 1) (R 1) [50,65,192,272,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b599
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P01
