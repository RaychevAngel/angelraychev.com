import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0001

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b540 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 265 48 160 82 210 338), lower := (rows 113 14 133 265 48 160 64 128 256), losses := [] }

theorem u540 : Upper (D 0) (R 0) [112,12,129,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b540
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b541 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 133 265 80 160 114 178 306), lower := (rows 113 14 133 265 80 160 64 128 256), losses := [] }

theorem u541 : Upper (D 0) (R 0) [112,12,129,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b541
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b542 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 14 133 280 17 34 224 224 480), lower := (rows 113 14 133 280 17 34 64 128 256), losses := [] }

theorem u542 : Upper (D 0) (R 0) [112,12,129,272,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b542
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b543 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 133 280 17 96 226 162 418), lower := (rows 113 14 133 280 17 96 64 128 256), losses := [] }

theorem u543 : Upper (D 0) (R 0) [112,12,129,272,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b543
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m544_2 : Upper (D 0) (R 0) [112,12,129,272,1,128,2] 13 :=
  permutation_upper _ _ _ [112,12,129,272,1,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u76

theorem m544_32 : Upper (D 0) (R 0) [112,12,129,272,1,128,32] 13 :=
  permutation_upper _ _ _ [112,12,129,272,1,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u77

def r544 : Route 9 := (fun mask => (mask,id))

def c544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u544 : Upper (D 0) (R 0) [112,12,129,272,1,128] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,1,128] 13 (by decide) (choices 1) [2,32] r544 c544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m544_2
  · exact m544_32

def r545 : Route 9 := (fun mask => (mask,id))

def c545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u545 : Upper (D 0) (R 0) [112,12,129,272,128,1] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,128,1] 13 (by decide) (choices 1) [2,32] r545 c545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u78
  · exact u79

def b546 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 113 14 133 280 144 34 97 225 353), lower := (rows 113 14 133 280 144 34 64 128 256), losses := [] }

theorem u546 : Upper (D 0) (R 0) [112,12,129,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b546
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 133 280 144 96 99 163 291), lower := (rows 113 14 133 280 144 96 64 128 256), losses := [] }

theorem u547 : Upper (D 0) (R 0) [112,12,129,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b547
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 14 148 265 17 34 224 224 480), lower := (rows 113 14 148 265 17 34 64 128 256), losses := [] }

theorem u548 : Upper (D 0) (R 0) [112,12,144,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b548
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b549 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 148 265 17 96 226 162 418), lower := (rows 113 14 148 265 17 96 64 128 256), losses := [] }

theorem u549 : Upper (D 0) (R 0) [112,12,144,257,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b549
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m550_2 : Upper (D 0) (R 0) [112,12,144,257,1,128,2] 13 :=
  permutation_upper _ _ _ [112,12,144,257,1,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u80

theorem m550_32 : Upper (D 0) (R 0) [112,12,144,257,1,128,32] 13 :=
  permutation_upper _ _ _ [112,12,144,257,1,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u81

def r550 : Route 9 := (fun mask => (mask,id))

def c550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u550 : Upper (D 0) (R 0) [112,12,144,257,1,128] 13 := by
  apply FastRouting.sound _ _ [112,12,144,257,1,128] 13 (by decide) (choices 1) [2,32] r550 c550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m550_2
  · exact m550_32

def b551 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 14 148 296 17 33 194 194 450), lower := (rows 113 14 148 296 17 33 64 128 256), losses := [] }

theorem u551 : Upper (D 0) (R 0) [112,12,144,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b551
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b552 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 14 148 296 17 34 193 193 449), lower := (rows 113 14 148 296 17 34 64 128 256), losses := [] }

theorem u552 : Upper (D 0) (R 0) [112,12,144,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b552
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b553 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 14 148 296 17 96 195 131 387), lower := (rows 113 14 148 296 17 96 64 128 256), losses := [] }

theorem u553 : Upper (D 0) (R 0) [112,12,144,288,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b553
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r554 : Route 9 := (fun mask => (mask,id))

def c554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u554 : Upper (D 0) (R 0) [112,12,144,288,1,128] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288,1,128] 13 (by decide) (choices 1) [1,2] r554 c554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u82
  · exact u83

def b555 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 44 200 17 33 450 386 386), lower := (rows 113 22 44 200 17 33 64 128 256), losses := [] }

theorem u555 : Upper (D 0) (R 0) [112,20,40,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b555
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 113 22 44 200 17 34 449 385 385), lower := (rows 113 22 44 200 17 34 64 128 256), losses := [] }

theorem u556 : Upper (D 0) (R 0) [112,20,40,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b556
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b557 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 113 22 44 200 17 160 323 387 259), lower := (rows 113 22 44 200 17 160 64 128 256), losses := [] }

theorem u557 : Upper (D 0) (R 0) [112,20,40,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b557
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b558 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 44 200 17 288 195 131 387), lower := (rows 113 22 44 200 17 288 64 128 256), losses := [] }

theorem u558 : Upper (D 0) (R 0) [112,20,40,192,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b558
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 265 144 33 194 194 450), lower := (rows 113 22 44 265 144 33 64 128 256), losses := [] }

theorem u559 : Upper (D 0) (R 0) [112,20,40,257,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b559
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b560 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 44 265 144 34 193 193 449), lower := (rows 113 22 44 265 144 34 64 128 256), losses := [] }

theorem u560 : Upper (D 0) (R 0) [112,20,40,257,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b560
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b561 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 265 144 96 195 131 387), lower := (rows 113 22 44 265 144 96 64 128 256), losses := [] }

theorem u561 : Upper (D 0) (R 0) [112,20,40,257,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b561
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 265 144 160 67 195 323), lower := (rows 113 22 44 265 144 160 64 128 256), losses := [] }

theorem u562 : Upper (D 0) (R 0) [112,20,40,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b562
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 193, camps := [], pairs := [(1,5)], upper := (rows 113 22 44 266 144 33 193 193 449), lower := (rows 113 22 44 266 144 33 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 181 0 97 161 289), good := (rows 465 30 478 266 144 465 64 144 256) }] }

theorem u563 : Upper (D 0) (R 0) [112,20,40,258,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b563
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 266 144 96 193 129 385), lower := (rows 113 22 44 266 144 96 64 128 256), losses := [] }

theorem u564 : Upper (D 0) (R 0) [112,20,40,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b564
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 266 144 160 65 193 321), lower := (rows 113 22 44 266 144 160 64 128 256), losses := [] }

theorem u565 : Upper (D 0) (R 0) [112,20,40,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b565
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 44 328 17 33 194 130 386), lower := (rows 113 22 44 328 17 33 64 128 256), losses := [] }

theorem u566 : Upper (D 0) (R 0) [112,20,40,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b566
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 113 22 44 328 17 34 193 129 385), lower := (rows 113 22 44 328 17 34 64 128 256), losses := [] }

theorem u567 : Upper (D 0) (R 0) [112,20,40,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b567
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r568 : Route 9 := (fun mask => (mask,id))

def c568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u568 : Upper (D 0) (R 0) [112,20,40,320,1,128] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320,1,128] 13 (by decide) (choices 1) [1,2,128] r568 c568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u84
  · exact u85
  · exact u86

def r569 : Route 9 := (fun mask => (mask,id))

def c569 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u569 : Upper (D 0) (R 0) [112,20,40,320,128,1] 13 := by
  apply FastRouting.sound _ _ [112,20,40,320,128,1] 13 (by decide) (choices 1) [1,2,128] r569 c569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u87
  · exact u88
  · exact u89

def b570 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 113 22 44 328 144 34 193 129 385), lower := (rows 113 22 44 328 144 34 64 128 256), losses := [] }

theorem u570 : Upper (D 0) (R 0) [112,20,40,320,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b570
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 328 144 160 67 131 259), lower := (rows 113 22 44 328 144 160 64 128 256), losses := [] }

theorem u571 : Upper (D 0) (R 0) [112,20,40,320,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b571
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 44 392 17 33 194 194 450), lower := (rows 113 22 44 392 17 33 64 128 256), losses := [] }

theorem u572 : Upper (D 0) (R 0) [112,20,40,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b572
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 44 392 17 34 193 193 449), lower := (rows 113 22 44 392 17 34 64 128 256), losses := [] }

theorem u573 : Upper (D 0) (R 0) [112,20,40,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b573
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 44 392 17 96 195 131 387), lower := (rows 113 22 44 392 17 96 64 128 256), losses := [] }

theorem u574 : Upper (D 0) (R 0) [112,20,40,384,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b574
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 113 22 44 392 17 160 67 195 323), lower := (rows 113 22 44 392 17 160 64 128 256), losses := [] }

theorem u575 : Upper (D 0) (R 0) [112,20,40,384,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b575
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 140 296 17 33 194 194 450), lower := (rows 113 22 140 296 17 33 64 128 256), losses := [] }

theorem u576 : Upper (D 0) (R 0) [112,20,136,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b576
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 140 296 17 34 193 193 449), lower := (rows 113 22 140 296 17 34 64 128 256), losses := [] }

theorem u577 : Upper (D 0) (R 0) [112,20,136,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b577
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 140 296 17 96 195 131 387), lower := (rows 113 22 140 296 17 96 64 128 256), losses := [] }

theorem u578 : Upper (D 0) (R 0) [112,20,136,288,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b578
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r579 : Route 9 := (fun mask => (mask,id))

def c579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u579 : Upper (D 0) (R 0) [112,20,136,288,1,128] 13 := by
  apply FastRouting.sound _ _ [112,20,136,288,1,128] 13 (by decide) (choices 1) [1,2] r579 c579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u90
  · exact u91

def b580 : PairBound 9 := { available := 328, camps := [], pairs := [], upper := (rows 113 22 164 137 17 34 328 456 328), lower := (rows 113 22 164 137 17 34 64 128 256), losses := [] }

theorem u580 : Upper (D 0) (R 0) [112,20,160,129,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b580
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 322, camps := [], pairs := [], upper := (rows 113 22 164 137 17 40 322 450 322), lower := (rows 113 22 164 137 17 40 64 128 256), losses := [] }

theorem u581 : Upper (D 0) (R 0) [112,20,160,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b581
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 137 17 96 330 394 266), lower := (rows 113 22 164 137 17 96 64 128 256), losses := [] }

theorem u582 : Upper (D 0) (R 0) [112,20,160,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b582
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b583 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 22 164 137 17 288 74 202 330), lower := (rows 113 22 164 137 17 288 64 128 256), losses := [] }

theorem u583 : Upper (D 0) (R 0) [112,20,160,129,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b583
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b584 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 200 17 33 330 394 266), lower := (rows 113 22 164 200 17 33 64 128 256), losses := [] }

theorem u584 : Upper (D 0) (R 0) [112,20,160,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b584
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 113 22 164 200 17 34 329 393 265), lower := (rows 113 22 164 200 17 34 64 128 256), losses := [] }

theorem u585 : Upper (D 0) (R 0) [112,20,160,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b585
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 113 22 164 200 17 40 323 387 259), lower := (rows 113 22 164 200 17 40 64 128 256), losses := [] }

theorem u586 : Upper (D 0) (R 0) [112,20,160,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b586
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b587 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 22 164 200 17 288 75 139 267), lower := (rows 113 22 164 200 17 288 64 128 256), losses := [] }

theorem u587 : Upper (D 0) (R 0) [112,20,160,192,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b587
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b588 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 113 22 164 265 17 34 200 200 456), lower := (rows 113 22 164 265 17 34 64 128 256), losses := [] }

theorem u588 : Upper (D 0) (R 0) [112,20,160,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b588
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b589 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 22 164 265 17 40 194 194 450), lower := (rows 113 22 164 265 17 40 64 128 256), losses := [] }

theorem u589 : Upper (D 0) (R 0) [112,20,160,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b589
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b590 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 265 17 96 202 138 394), lower := (rows 113 22 164 265 17 96 64 128 256), losses := [] }

theorem u590 : Upper (D 0) (R 0) [112,20,160,257,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b590
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 265 17 160 74 202 330), lower := (rows 113 22 164 265 17 160 64 128 256), losses := [] }

theorem u591 : Upper (D 0) (R 0) [112,20,160,257,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b591
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b592 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 266 17 33 200 200 456), lower := (rows 113 22 164 266 17 33 64 128 256), losses := [] }

theorem u592 : Upper (D 0) (R 0) [112,20,160,258,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b592
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b593 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 22 164 266 17 40 193 193 449), lower := (rows 113 22 164 266 17 40 64 128 256), losses := [] }

theorem u593 : Upper (D 0) (R 0) [112,20,160,258,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b593
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b594 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 266 17 96 201 137 393), lower := (rows 113 22 164 266 17 96 64 128 256), losses := [] }

theorem u594 : Upper (D 0) (R 0) [112,20,160,258,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b594
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b595 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 266 17 160 73 201 329), lower := (rows 113 22 164 266 17 160 64 128 256), losses := [] }

theorem u595 : Upper (D 0) (R 0) [112,20,160,258,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b595
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0)], upper := (rows 113 22 164 328 17 33 202 138 394), lower := (rows 113 22 164 328 17 33 64 128 256), losses := [] }

theorem u596 : Upper (D 0) (R 0) [112,20,160,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b596
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 113 22 164 328 17 34 201 137 393), lower := (rows 113 22 164 328 17 34 64 128 256), losses := [] }

theorem u597 : Upper (D 0) (R 0) [112,20,160,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b597
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 164 328 17 40 195 131 387), lower := (rows 113 22 164 328 17 40 64 128 256), losses := [] }

theorem u598 : Upper (D 0) (R 0) [112,20,160,320,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b598
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 328 17 160 75 139 267), lower := (rows 113 22 164 328 17 160 64 128 256), losses := [] }

theorem u599 : Upper (D 0) (R 0) [112,20,160,320,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b599
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P00
