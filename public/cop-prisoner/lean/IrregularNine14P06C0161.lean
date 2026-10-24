import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0017
import IrregularNine14P06C0018

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9660 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 133 104 336 48 78 142 270), lower := (rows 7 35 133 104 336 48 64 128 256), losses := [] }

theorem u9660 : Upper (D 6) (R 6) [6,33,129,96,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9660
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9661 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 25 336 34 100 228 356), lower := (rows 7 35 140 25 336 34 64 128 256), losses := [] }

theorem u9661 : Upper (D 6) (R 6) [6,33,136,17,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9661
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9662 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 25 336 36 98 226 354), lower := (rows 7 35 140 25 336 36 64 128 256), losses := [] }

theorem u9662 : Upper (D 6) (R 6) [6,33,136,17,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9662
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9663 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 140 25 336 96 102 166 294), lower := (rows 7 35 140 25 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 123 65 129 257), good := (rows 502 498 188 508 368 96 96 128 256) },{ target := 2, region := (rows 1 10 0 8 16 112 64 128 256), good := (rows 3 35 138 59 368 96 96 128 256) }] }

theorem u9663 : Upper (D 6) (R 6) [6,33,136,17,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9663
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9664 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 26 336 33 100 228 356), lower := (rows 7 35 140 26 336 33 64 128 256), losses := [] }

theorem u9664 : Upper (D 6) (R 6) [6,33,136,18,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9664
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9665 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 26 336 36 97 225 353), lower := (rows 7 35 140 26 336 36 64 128 256), losses := [] }

theorem u9665 : Upper (D 6) (R 6) [6,33,136,18,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9665
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9666 : Route 9 := (fun mask => (mask,id))

def c9666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9666 : Upper (D 6) (R 6) [6,33,136,18,320,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,18,320,64] 13 (by decide) (choices 1) [1,4,32] r9666 c9666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1076
  · exact u1077
  · exact u1078

def b9667 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 28 112 33 322 450 322), lower := (rows 7 35 140 28 112 33 64 128 256), losses := [] }

theorem u9667 : Upper (D 6) (R 6) [6,33,136,20,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9667
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9668 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 28 112 34 321 449 321), lower := (rows 7 35 140 28 112 34 64 128 256), losses := [] }

theorem u9668 : Upper (D 6) (R 6) [6,33,136,20,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9668
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9669 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 28 112 96 323 387 259), lower := (rows 7 35 140 28 112 96 64 128 256), losses := [] }

theorem u9669 : Upper (D 6) (R 6) [6,33,136,20,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9669
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9670 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 28 112 288 67 195 323), lower := (rows 7 35 140 28 112 288 64 128 256), losses := [] }

theorem u9670 : Upper (D 6) (R 6) [6,33,136,20,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9670
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9671 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 28 304 33 66 194 322), lower := (rows 7 35 140 28 304 33 64 128 256), losses := [] }

theorem u9671 : Upper (D 6) (R 6) [6,33,136,20,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9671
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9672 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 28 304 34 65 193 321), lower := (rows 7 35 140 28 304 34 64 128 256), losses := [] }

theorem u9672 : Upper (D 6) (R 6) [6,33,136,20,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9672
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9673 : Route 9 := (fun mask => (mask,id))

def c9673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9673 : Upper (D 6) (R 6) [6,33,136,20,288,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,288,64] 13 (by decide) (choices 1) [1,2] r9673 c9673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1079
  · exact u1080

def b9674 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 28 336 33 98 226 354), lower := (rows 7 35 140 28 336 33 64 128 256), losses := [] }

theorem u9674 : Upper (D 6) (R 6) [6,33,136,20,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9674
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9675 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 28 336 34 97 225 353), lower := (rows 7 35 140 28 336 34 64 128 256), losses := [] }

theorem u9675 : Upper (D 6) (R 6) [6,33,136,20,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9675
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9676 : Route 9 := (fun mask => (mask,id))

def c9676 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9676 : Upper (D 6) (R 6) [6,33,136,20,320,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,320,64] 13 (by decide) (choices 1) [1,2,32] r9676 c9676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1081
  · exact u1082
  · exact u1083

def b9677 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 56 82 33 324 452 324), lower := (rows 7 35 140 56 82 33 64 128 256), losses := [] }

theorem u9677 : Upper (D 6) (R 6) [6,33,136,48,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9677
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9678 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 56 82 36 321 449 321), lower := (rows 7 35 140 56 82 36 64 128 256), losses := [] }

theorem u9678 : Upper (D 6) (R 6) [6,33,136,48,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9678
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9679 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 56 82 96 325 389 261), lower := (rows 7 35 140 56 82 96 64 128 256), losses := [] }

theorem u9679 : Upper (D 6) (R 6) [6,33,136,48,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9679
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9680 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 80, targets := 32 }], pairs := [(3,1),(4,5)], upper := (rows 7 35 140 56 82 288 69 197 325), lower := (rows 7 35 140 56 82 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 291 65 129 257), good := (rows 485 481 140 56 120 288 64 128 288) }] }

theorem u9680 : Upper (D 6) (R 6) [6,33,136,48,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9680
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9681 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 56 84 33 322 450 322), lower := (rows 7 35 140 56 84 33 64 128 256), losses := [] }

theorem u9681 : Upper (D 6) (R 6) [6,33,136,48,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9681
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9682 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 56 84 34 321 449 321), lower := (rows 7 35 140 56 84 34 64 128 256), losses := [] }

theorem u9682 : Upper (D 6) (R 6) [6,33,136,48,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9682
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9683 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 56 84 96 323 387 259), lower := (rows 7 35 140 56 84 96 64 128 256), losses := [] }

theorem u9683 : Upper (D 6) (R 6) [6,33,136,48,68,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9683
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9684 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,5)], upper := (rows 7 35 140 56 84 288 67 195 323), lower := (rows 7 35 140 56 84 288 64 128 256), losses := [] }

theorem u9684 : Upper (D 6) (R 6) [6,33,136,48,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9684
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9685 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 56 274 33 68 196 324), lower := (rows 7 35 140 56 274 33 64 128 256), losses := [] }

theorem u9685 : Upper (D 6) (R 6) [6,33,136,48,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9685
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9686 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 56 274 36 65 193 321), lower := (rows 7 35 140 56 274 36 64 128 256), losses := [] }

theorem u9686 : Upper (D 6) (R 6) [6,33,136,48,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9686
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9687 : Route 9 := (fun mask => (mask,id))

def c9687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9687 : Upper (D 6) (R 6) [6,33,136,48,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,258,64] 13 (by decide) (choices 1) [1,4] r9687 c9687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1084
  · exact u1085

def b9688 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 56 276 33 66 194 322), lower := (rows 7 35 140 56 276 33 64 128 256), losses := [] }

theorem u9688 : Upper (D 6) (R 6) [6,33,136,48,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9688
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9689 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 56 276 34 65 193 321), lower := (rows 7 35 140 56 276 34 64 128 256), losses := [] }

theorem u9689 : Upper (D 6) (R 6) [6,33,136,48,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9689
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9690 : Route 9 := (fun mask => (mask,id))

def c9690 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9690 : Upper (D 6) (R 6) [6,33,136,48,260,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,260,64] 13 (by decide) (choices 1) [1,2] r9690 c9690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1086
  · exact u1087

def b9691 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 56 336 33 70 198 326), lower := (rows 7 35 140 56 336 33 64 128 256), losses := [] }

theorem u9691 : Upper (D 6) (R 6) [6,33,136,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9691
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9692 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 56 336 34 69 197 325), lower := (rows 7 35 140 56 336 34 64 128 256), losses := [] }

theorem u9692 : Upper (D 6) (R 6) [6,33,136,48,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9692
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9693 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 56 336 36 67 195 323), lower := (rows 7 35 140 56 336 36 64 128 256), losses := [] }

theorem u9693 : Upper (D 6) (R 6) [6,33,136,48,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9693
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9694 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 56 336 96 71 135 263), lower := (rows 7 35 140 56 336 96 64 128 256), losses := [] }

theorem u9694 : Upper (D 6) (R 6) [6,33,136,48,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9694
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9695 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 73 82 36 368 432 304), lower := (rows 7 35 140 73 82 36 64 128 256), losses := [] }

theorem u9695 : Upper (D 6) (R 6) [6,33,136,65,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9695
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9696 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 140 73 82 48 356 420 292), lower := (rows 7 35 140 73 82 48 64 128 256), losses := [] }

theorem u9696 : Upper (D 6) (R 6) [6,33,136,65,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9696
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9697 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 140 73 82 288 116 180 308), lower := (rows 7 35 140 73 82 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 303 73 137 265), good := (rows 502 498 492 508 114 288 64 128 288) }] }

theorem u9697 : Upper (D 6) (R 6) [6,33,136,65,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9697
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9698 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 73 112 34 340 404 276), lower := (rows 7 35 140 73 112 34 64 128 256), losses := [] }

theorem u9698 : Upper (D 6) (R 6) [6,33,136,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9698
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9699 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 73 112 36 338 402 274), lower := (rows 7 35 140 73 112 36 64 128 256), losses := [] }

theorem u9699 : Upper (D 6) (R 6) [6,33,136,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9699
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9700 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 73 112 48 326 390 262), lower := (rows 7 35 140 73 112 48 64 128 256), losses := [] }

theorem u9700 : Upper (D 6) (R 6) [6,33,136,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9700
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9701 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 140 73 112 288 86 150 278), lower := (rows 7 35 140 73 112 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 299 65 129 257), good := (rows 502 498 188 508 112 288 64 128 288) }] }

theorem u9701 : Upper (D 6) (R 6) [6,33,136,65,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9701
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9702 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 73 274 36 112 240 368), lower := (rows 7 35 140 73 274 36 64 128 256), losses := [] }

theorem u9702 : Upper (D 6) (R 6) [6,33,136,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9702
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9703 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 140 73 274 48 100 228 356), lower := (rows 7 35 140 73 274 48 64 128 256), losses := [] }

theorem u9703 : Upper (D 6) (R 6) [6,33,136,65,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9703
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9704 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 140 73 274 96 116 180 308), lower := (rows 7 35 140 73 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 111 73 137 265), good := (rows 502 498 492 508 306 96 96 128 256) }] }

theorem u9704 : Upper (D 6) (R 6) [6,33,136,65,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9704
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9705 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 73 276 34 112 240 368), lower := (rows 7 35 140 73 276 34 64 128 256), losses := [] }

theorem u9705 : Upper (D 6) (R 6) [6,33,136,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9705
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9706 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 73 276 48 98 226 354), lower := (rows 7 35 140 73 276 48 64 128 256), losses := [] }

theorem u9706 : Upper (D 6) (R 6) [6,33,136,65,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9706
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9707 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 140 73 276 96 114 178 306), lower := (rows 7 35 140 73 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 107 67 131 259), good := (rows 502 498 188 508 276 96 96 128 256) }] }

theorem u9707 : Upper (D 6) (R 6) [6,33,136,65,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9707
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9708 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 73 304 34 84 212 340), lower := (rows 7 35 140 73 304 34 64 128 256), losses := [] }

theorem u9708 : Upper (D 6) (R 6) [6,33,136,65,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9708
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9709 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 73 304 36 82 210 338), lower := (rows 7 35 140 73 304 36 64 128 256), losses := [] }

theorem u9709 : Upper (D 6) (R 6) [6,33,136,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9709
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9710 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 140 73 304 48 70 198 326), lower := (rows 7 35 140 73 304 48 64 128 256), losses := [] }

theorem u9710 : Upper (D 6) (R 6) [6,33,136,65,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9710
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9711 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 140 73 304 96 86 150 278), lower := (rows 7 35 140 73 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 107 65 129 257), good := (rows 502 498 188 508 304 96 96 128 256) }] }

theorem u9711 : Upper (D 6) (R 6) [6,33,136,65,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9711
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9712 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 73 336 34 116 180 308), lower := (rows 7 35 140 73 336 34 64 128 256), losses := [] }

theorem u9712 : Upper (D 6) (R 6) [6,33,136,65,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9712
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9713 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 73 336 36 114 178 306), lower := (rows 7 35 140 73 336 36 64 128 256), losses := [] }

theorem u9713 : Upper (D 6) (R 6) [6,33,136,65,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9713
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9714 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 140 73 336 48 102 166 294), lower := (rows 7 35 140 73 336 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 63 65 129 257), good := (rows 502 498 188 508 368 48 64 128 256) }] }

theorem u9714 : Upper (D 6) (R 6) [6,33,136,65,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9714
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9715 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 74 81 36 368 432 304), lower := (rows 7 35 140 74 81 36 64 128 256), losses := [] }

theorem u9715 : Upper (D 6) (R 6) [6,33,136,66,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9715
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9716 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 140 74 81 48 356 420 292), lower := (rows 7 35 140 74 81 48 64 128 256), losses := [] }

theorem u9716 : Upper (D 6) (R 6) [6,33,136,66,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9716
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9717 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 140 74 81 288 116 180 308), lower := (rows 7 35 140 74 81 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 319 73 137 265), good := (rows 501 497 492 508 497 288 64 128 288) }] }

theorem u9717 : Upper (D 6) (R 6) [6,33,136,66,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9717
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9718 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 74 112 33 340 404 276), lower := (rows 7 35 140 74 112 33 64 128 256), losses := [] }

theorem u9718 : Upper (D 6) (R 6) [6,33,136,66,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9718
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9719 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 74 112 36 337 401 273), lower := (rows 7 35 140 74 112 36 64 128 256), losses := [] }

theorem u9719 : Upper (D 6) (R 6) [6,33,136,66,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9719
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9719
end Delivery.IrregularNine14.P06
