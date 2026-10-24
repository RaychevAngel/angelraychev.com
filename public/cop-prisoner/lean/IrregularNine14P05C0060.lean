import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0018

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3600 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 140 280 33 106 170 298), lower := (rows 19 38 69 140 280 33 64 128 256), losses := [] }

theorem u3600 : Upper (D 5) (R 5) [18,36,65,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3601 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 140 280 34 105 169 297), lower := (rows 19 38 69 140 280 34 64 128 256), losses := [] }

theorem u3601 : Upper (D 5) (R 5) [18,36,65,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3602 : Route 9 := (fun mask => (mask,id))

def c3602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3602 : Upper (D 5) (R 5) [18,36,65,132,264,8] 13 := by
  apply FastRouting.sound _ _ [18,36,65,132,264,8] 13 (by decide) (choices 1) [1,2,32] r3602 c3602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1094
  · exact u1095
  · exact u1096

def b3603 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 168 28 33 330 394 266), lower := (rows 19 38 69 168 28 33 64 128 256), losses := [] }

theorem u3603 : Upper (D 5) (R 5) [18,36,65,160,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3604 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 168 28 34 329 393 265), lower := (rows 19 38 69 168 28 34 64 128 256), losses := [] }

theorem u3604 : Upper (D 5) (R 5) [18,36,65,160,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3605 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 69 168 28 40 323 387 259), lower := (rows 19 38 69 168 28 40 64 128 256), losses := [] }

theorem u3605 : Upper (D 5) (R 5) [18,36,65,160,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3606 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(3,2)], upper := (rows 19 38 69 168 28 288 75 139 267), lower := (rows 19 38 69 168 28 288 64 128 256), losses := [] }

theorem u3606 : Upper (D 5) (R 5) [18,36,65,160,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3606
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 168 276 33 74 138 266), lower := (rows 19 38 69 168 276 33 64 128 256), losses := [] }

theorem u3607 : Upper (D 5) (R 5) [18,36,65,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3608 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 168 276 34 73 137 265), lower := (rows 19 38 69 168 276 34 64 128 256), losses := [] }

theorem u3608 : Upper (D 5) (R 5) [18,36,65,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3608
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3609 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 69 168 276 40 75 139 267), lower := (rows 19 38 69 168 276 40 64 128 256), losses := [] }

theorem u3609 : Upper (D 5) (R 5) [18,36,65,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 168 280 33 78 142 270), lower := (rows 19 38 69 168 280 33 64 128 256), losses := [] }

theorem u3610 : Upper (D 5) (R 5) [18,36,65,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3611 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 168 280 34 77 141 269), lower := (rows 19 38 69 168 280 34 64 128 256), losses := [] }

theorem u3611 : Upper (D 5) (R 5) [18,36,65,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 69 168 280 36 75 139 267), lower := (rows 19 38 69 168 280 36 64 128 256), losses := [] }

theorem u3612 : Upper (D 5) (R 5) [18,36,65,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 69 168 280 40 71 135 263), lower := (rows 19 38 69 168 280 40 64 128 256), losses := [] }

theorem u3613 : Upper (D 5) (R 5) [18,36,65,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3614 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 69 392 28 33 106 170 298), lower := (rows 19 38 69 392 28 33 64 128 256), losses := [] }

theorem u3614 : Upper (D 5) (R 5) [18,36,65,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3615 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 69 392 28 34 105 169 297), lower := (rows 19 38 69 392 28 34 64 128 256), losses := [] }

theorem u3615 : Upper (D 5) (R 5) [18,36,65,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(3,2)], upper := (rows 19 38 69 392 28 40 99 163 291), lower := (rows 19 38 69 392 28 40 64 128 256), losses := [] }

theorem u3616 : Upper (D 5) (R 5) [18,36,65,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 41 152 33 332 396 268), lower := (rows 19 38 70 41 152 33 64 128 256), losses := [] }

theorem u3617 : Upper (D 5) (R 5) [18,36,66,33,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3618 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 41 152 36 329 393 265), lower := (rows 19 38 70 41 152 36 64 128 256), losses := [] }

theorem u3618 : Upper (D 5) (R 5) [18,36,66,33,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3619 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 41 152 40 325 389 261), lower := (rows 19 38 70 41 152 40 64 128 256), losses := [] }

theorem u3619 : Upper (D 5) (R 5) [18,36,66,33,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3619
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3620 : Route 9 := (fun mask => (mask,id))

def c3620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3620 : Upper (D 5) (R 5) [18,36,66,33,136,256] 13 := by
  apply FastRouting.sound _ _ [18,36,66,33,136,256] 13 (by decide) (choices 1) [1,4,8] r3620 c3620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099

def b3621 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 41 400 33 76 140 268), lower := (rows 19 38 70 41 400 33 64 128 256), losses := [] }

theorem u3621 : Upper (D 5) (R 5) [18,36,66,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3622 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 41 400 36 73 137 265), lower := (rows 19 38 70 41 400 36 64 128 256), losses := [] }

theorem u3622 : Upper (D 5) (R 5) [18,36,66,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3623 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 41 400 40 77 141 269), lower := (rows 19 38 70 41 400 40 64 128 256), losses := [] }

theorem u3623 : Upper (D 5) (R 5) [18,36,66,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3624 : Route 9 := (fun mask => (mask,id))

def c3624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3624 : Upper (D 5) (R 5) [18,36,66,129,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,66,129,264,1] 13 (by decide) (choices 1) [4,8,32] r3624 c3624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1100
  · exact u1101
  · exact u1102

def b3625 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 137 280 36 105 169 297), lower := (rows 19 38 70 137 280 36 64 128 256), losses := [] }

theorem u3625 : Upper (D 5) (R 5) [18,36,66,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3625
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3626 : Route 9 := (fun mask => (mask,id))

def c3626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3626 : Upper (D 5) (R 5) [18,36,66,129,264,8] 13 := by
  apply FastRouting.sound _ _ [18,36,66,129,264,8] 13 (by decide) (choices 1) [1,4,32] r3626 c3626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1103
  · exact u1104
  · exact u1105

def b3627 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 140 25 33 360 424 296), lower := (rows 19 38 70 140 25 33 64 128 256), losses := [] }

theorem u3627 : Upper (D 5) (R 5) [18,36,66,132,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3628 : Route 9 := (fun mask => (mask,id))

def c3628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3628 : Upper (D 5) (R 5) [18,36,66,132,9,8] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,9,8] 13 (by decide) (choices 1) [1,32,256] r3628 c3628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1106
  · exact u1107
  · exact u1108

def r3629 : Route 9 := (fun mask => (mask,id))

def c3629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3629 : Upper (D 5) (R 5) [18,36,66,132,9,256] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,9,256] 13 (by decide) (choices 1) [1,8,32] r3629 c3629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1109
  · exact u1110
  · exact u1111

def b3630 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 140 273 33 104 168 296), lower := (rows 19 38 70 140 273 33 64 128 256), losses := [] }

theorem u3630 : Upper (D 5) (R 5) [18,36,66,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3631 : Route 9 := (fun mask => (mask,id))

def c3631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3631 : Upper (D 5) (R 5) [18,36,66,132,257,8] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,257,8] 13 (by decide) (choices 1) [1,8,32] r3631 c3631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1112
  · exact u1113
  · exact u1114

def r3632 : Route 9 := (fun mask => (mask,id))

def c3632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3632 : Upper (D 5) (R 5) [18,36,66,132,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,264,1] 13 (by decide) (choices 1) [1,8,32] r3632 c3632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1115
  · exact u1116
  · exact u1117

def r3633 : Route 9 := (fun mask => (mask,id))

def c3633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3633 : Upper (D 5) (R 5) [18,36,66,132,264,8] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132,264,8] 13 (by decide) (choices 1) [1,32] r3633 c3633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1118
  · exact u1119

def b3634 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 168 25 33 332 396 268), lower := (rows 19 38 70 168 25 33 64 128 256), losses := [] }

theorem u3634 : Upper (D 5) (R 5) [18,36,66,160,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 168 25 36 329 393 265), lower := (rows 19 38 70 168 25 36 64 128 256), losses := [] }

theorem u3635 : Upper (D 5) (R 5) [18,36,66,160,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3636 : PairBound 9 := { available := 261, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 70 168 25 40 325 389 261), lower := (rows 19 38 70 168 25 40 64 128 256), losses := [] }

theorem u3636 : Upper (D 5) (R 5) [18,36,66,160,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3637 : PairBound 9 := { available := 13, camps := [], pairs := [(2,5)], upper := (rows 19 38 70 168 25 288 77 141 269), lower := (rows 19 38 70 168 25 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 80 144 272), good := (rows 471 6 70 136 477 256 64 128 256) }] }

theorem u3637 : Upper (D 5) (R 5) [18,36,66,160,9,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 168 273 33 76 140 268), lower := (rows 19 38 70 168 273 33 64 128 256), losses := [] }

theorem u3638 : Upper (D 5) (R 5) [18,36,66,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 168 273 36 73 137 265), lower := (rows 19 38 70 168 273 36 64 128 256), losses := [] }

theorem u3639 : Upper (D 5) (R 5) [18,36,66,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3639
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3640 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 70 168 273 40 77 141 269), lower := (rows 19 38 70 168 273 40 64 128 256), losses := [] }

theorem u3640 : Upper (D 5) (R 5) [18,36,66,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3641 : Route 9 := (fun mask => (mask,id))

def c3641 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3641 : Upper (D 5) (R 5) [18,36,66,160,264,1] 13 := by
  apply FastRouting.sound _ _ [18,36,66,160,264,1] 13 (by decide) (choices 1) [1,4,8] r3641 c3641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1120
  · exact u1121
  · exact u1122

def b3642 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 168 280 36 73 137 265), lower := (rows 19 38 70 168 280 36 64 128 256), losses := [] }

theorem u3642 : Upper (D 5) (R 5) [18,36,66,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3643 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 38 70 168 280 40 69 133 261), lower := (rows 19 38 70 168 280 40 64 128 256), losses := [] }

theorem u3643 : Upper (D 5) (R 5) [18,36,66,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3644 : PairBound 9 := { available := 44, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 392 25 33 108 172 300), lower := (rows 19 38 70 392 25 33 64 128 256), losses := [] }

theorem u3644 : Upper (D 5) (R 5) [18,36,66,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3645 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 392 25 36 105 169 297), lower := (rows 19 38 70 392 25 36 64 128 256), losses := [] }

theorem u3645 : Upper (D 5) (R 5) [18,36,66,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3645
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3646 : Route 9 := (fun mask => (mask,id))

def c3646 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3646 : Upper (D 5) (R 5) [18,36,66,384,9,8] 13 := by
  apply FastRouting.sound _ _ [18,36,66,384,9,8] 13 (by decide) (choices 1) [1,4,32] r3646 c3646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1123
  · exact u1124
  · exact u1125

def b3647 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 41 148 33 330 394 266), lower := (rows 19 38 76 41 148 33 64 128 256), losses := [] }

theorem u3647 : Upper (D 5) (R 5) [18,36,72,33,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3647
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 76 41 148 34 329 393 265), lower := (rows 19 38 76 41 148 34 64 128 256), losses := [] }

theorem u3648 : Upper (D 5) (R 5) [18,36,72,33,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 401, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 41 148 40 323 387 259), lower := (rows 19 38 76 41 148 40 64 128 256), losses := [] }

theorem u3649 : Upper (D 5) (R 5) [18,36,72,33,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3650 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 38 76 41 148 288 75 139 267), lower := (rows 19 38 76 41 148 288 64 128 256), losses := [] }

theorem u3650 : Upper (D 5) (R 5) [18,36,72,33,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3651 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 41 152 33 326 390 262), lower := (rows 19 38 76 41 152 33 64 128 256), losses := [] }

theorem u3651 : Upper (D 5) (R 5) [18,36,72,33,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3652 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 76 41 152 34 325 389 261), lower := (rows 19 38 76 41 152 34 64 128 256), losses := [] }

theorem u3652 : Upper (D 5) (R 5) [18,36,72,33,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3653 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 41 152 36 323 387 259), lower := (rows 19 38 76 41 152 36 64 128 256), losses := [] }

theorem u3653 : Upper (D 5) (R 5) [18,36,72,33,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3654 : Route 9 := (fun mask => (mask,id))

def c3654 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3654 : Upper (D 5) (R 5) [18,36,72,33,136,256] 13 := by
  apply FastRouting.sound _ _ [18,36,72,33,136,256] 13 (by decide) (choices 1) [1,2,4] r3654 c3654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1126
  · exact u1127
  · exact u1128

def b3655 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 41 400 33 78 142 270), lower := (rows 19 38 76 41 400 33 64 128 256), losses := [] }

theorem u3655 : Upper (D 5) (R 5) [18,36,72,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3655
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 38 76 41 400 34 77 141 269), lower := (rows 19 38 76 41 400 34 64 128 256), losses := [] }

theorem u3656 : Upper (D 5) (R 5) [18,36,72,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 41 400 36 75 139 267), lower := (rows 19 38 76 41 400 36 64 128 256), losses := [] }

theorem u3657 : Upper (D 5) (R 5) [18,36,72,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 401, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 38 76 41 400 40 71 135 263), lower := (rows 19 38 76 41 400 40 64 128 256), losses := [] }

theorem u3658 : Upper (D 5) (R 5) [18,36,72,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 76 137 276 33 106 170 298), lower := (rows 19 38 76 137 276 33 64 128 256), losses := [] }

theorem u3659 : Upper (D 5) (R 5) [18,36,72,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3659
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P05
