import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0017

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9600 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 74 112 48 332 396 268), lower := (rows 7 35 133 74 112 48 64 128 256), losses := [] }

theorem u9600 : Upper (D 6) (R 6) [6,33,129,66,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9600
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9601 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 112 288 92 156 284), lower := (rows 7 35 133 74 112 288 64 128 256), losses := [] }

theorem u9601 : Upper (D 6) (R 6) [6,33,129,66,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9601
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9602 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 276 40 112 240 368), lower := (rows 7 35 133 74 276 40 64 128 256), losses := [] }

theorem u9602 : Upper (D 6) (R 6) [6,33,129,66,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9602
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9603 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 276 48 104 232 360), lower := (rows 7 35 133 74 276 48 64 128 256), losses := [] }

theorem u9603 : Upper (D 6) (R 6) [6,33,129,66,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9603
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9604 : Route 9 := (fun mask => (mask,id))

def c9604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9604 : Upper (D 6) (R 6) [6,33,129,66,260,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,260,64] 13 (by decide) (choices 1) [8,16,32] r9604 c9604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1049
  · exact u1050
  · exact u1051

def b9605 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 74 280 36 112 240 368), lower := (rows 7 35 133 74 280 36 64 128 256), losses := [] }

theorem u9605 : Upper (D 6) (R 6) [6,33,129,66,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9605
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9606 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 280 48 100 228 356), lower := (rows 7 35 133 74 280 48 64 128 256), losses := [] }

theorem u9606 : Upper (D 6) (R 6) [6,33,129,66,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9606
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9607 : Route 9 := (fun mask => (mask,id))

def c9607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9607 : Upper (D 6) (R 6) [6,33,129,66,264,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,264,64] 13 (by decide) (choices 1) [4,16,32] r9607 c9607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1052
  · exact u1053
  · exact u1054

def b9608 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 74 304 36 88 216 344), lower := (rows 7 35 133 74 304 36 64 128 256), losses := [] }

theorem u9608 : Upper (D 6) (R 6) [6,33,129,66,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9608
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9609 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 304 40 84 212 340), lower := (rows 7 35 133 74 304 40 64 128 256), losses := [] }

theorem u9609 : Upper (D 6) (R 6) [6,33,129,66,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9609
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9610 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 133 74 304 48 76 204 332), lower := (rows 7 35 133 74 304 48 64 128 256), losses := [] }

theorem u9610 : Upper (D 6) (R 6) [6,33,129,66,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9610
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9611 : Route 9 := (fun mask => (mask,id))

def c9611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9611 : Upper (D 6) (R 6) [6,33,129,66,288,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,288,64] 13 (by decide) (choices 1) [4,8,16] r9611 c9611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1055
  · exact u1056
  · exact u1057

def b9612 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 74 336 36 120 184 312), lower := (rows 7 35 133 74 336 36 64 128 256), losses := [] }

theorem u9612 : Upper (D 6) (R 6) [6,33,129,66,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9612
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9613 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 336 40 116 180 308), lower := (rows 7 35 133 74 336 40 64 128 256), losses := [] }

theorem u9613 : Upper (D 6) (R 6) [6,33,129,66,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9613
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9614 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 74 336 48 108 172 300), lower := (rows 7 35 133 74 336 48 64 128 256), losses := [] }

theorem u9614 : Upper (D 6) (R 6) [6,33,129,66,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9614
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9615 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 76 112 34 344 408 280), lower := (rows 7 35 133 76 112 34 64 128 256), losses := [] }

theorem u9615 : Upper (D 6) (R 6) [6,33,129,68,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9615
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9616 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 133 76 112 40 338 402 274), lower := (rows 7 35 133 76 112 40 64 128 256), losses := [] }

theorem u9616 : Upper (D 6) (R 6) [6,33,129,68,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9616
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9617 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 76 112 48 330 394 266), lower := (rows 7 35 133 76 112 48 64 128 256), losses := [] }

theorem u9617 : Upper (D 6) (R 6) [6,33,129,68,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9617
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9618 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 112 288 90 154 282), lower := (rows 7 35 133 76 112 288 64 128 256), losses := [] }

theorem u9618 : Upper (D 6) (R 6) [6,33,129,68,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9618
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9619 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 274 40 112 240 368), lower := (rows 7 35 133 76 274 40 64 128 256), losses := [] }

theorem u9619 : Upper (D 6) (R 6) [6,33,129,68,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9619
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9620 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 274 48 104 232 360), lower := (rows 7 35 133 76 274 48 64 128 256), losses := [] }

theorem u9620 : Upper (D 6) (R 6) [6,33,129,68,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9620
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9621 : Route 9 := (fun mask => (mask,id))

def c9621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9621 : Upper (D 6) (R 6) [6,33,129,68,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,258,64] 13 (by decide) (choices 1) [8,16,32] r9621 c9621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1058
  · exact u1059
  · exact u1060

def b9622 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 76 280 34 112 240 368), lower := (rows 7 35 133 76 280 34 64 128 256), losses := [] }

theorem u9622 : Upper (D 6) (R 6) [6,33,129,68,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9622
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9623 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 280 48 98 226 354), lower := (rows 7 35 133 76 280 48 64 128 256), losses := [] }

theorem u9623 : Upper (D 6) (R 6) [6,33,129,68,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9623
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9624 : Route 9 := (fun mask => (mask,id))

def c9624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9624 : Upper (D 6) (R 6) [6,33,129,68,264,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,264,64] 13 (by decide) (choices 1) [2,16,32] r9624 c9624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1061
  · exact u1062
  · exact u1063

def b9625 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 76 304 34 88 216 344), lower := (rows 7 35 133 76 304 34 64 128 256), losses := [] }

theorem u9625 : Upper (D 6) (R 6) [6,33,129,68,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9625
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9626 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 304 40 82 210 338), lower := (rows 7 35 133 76 304 40 64 128 256), losses := [] }

theorem u9626 : Upper (D 6) (R 6) [6,33,129,68,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9626
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9627 : PairBound 9 := { available := 74, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 133 76 304 48 74 202 330), lower := (rows 7 35 133 76 304 48 64 128 256), losses := [] }

theorem u9627 : Upper (D 6) (R 6) [6,33,129,68,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9627
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9628 : Route 9 := (fun mask => (mask,id))

def c9628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9628 : Upper (D 6) (R 6) [6,33,129,68,288,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,288,64] 13 (by decide) (choices 1) [2,8,16] r9628 c9628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1064
  · exact u1065
  · exact u1066

def b9629 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 76 336 34 120 184 312), lower := (rows 7 35 133 76 336 34 64 128 256), losses := [] }

theorem u9629 : Upper (D 6) (R 6) [6,33,129,68,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9629
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9630 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 336 40 114 178 306), lower := (rows 7 35 133 76 336 40 64 128 256), losses := [] }

theorem u9630 : Upper (D 6) (R 6) [6,33,129,68,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9630
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9631 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 76 336 48 106 170 298), lower := (rows 7 35 133 76 336 48 64 128 256), losses := [] }

theorem u9631 : Upper (D 6) (R 6) [6,33,129,68,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9631
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9632 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 88 274 36 104 232 360), lower := (rows 7 35 133 88 274 36 64 128 256), losses := [] }

theorem u9632 : Upper (D 6) (R 6) [6,33,129,80,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9632
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9633 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 88 274 40 100 228 356), lower := (rows 7 35 133 88 274 40 64 128 256), losses := [] }

theorem u9633 : Upper (D 6) (R 6) [6,33,129,80,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9633
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9634 : Route 9 := (fun mask => (mask,id))

def c9634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9634 : Upper (D 6) (R 6) [6,33,129,80,258,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,258,64] 13 (by decide) (choices 1) [4,8,32] r9634 c9634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1067
  · exact u1068
  · exact u1069

def b9635 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 88 276 34 104 232 360), lower := (rows 7 35 133 88 276 34 64 128 256), losses := [] }

theorem u9635 : Upper (D 6) (R 6) [6,33,129,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9635
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9636 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 88 276 40 98 226 354), lower := (rows 7 35 133 88 276 40 64 128 256), losses := [] }

theorem u9636 : Upper (D 6) (R 6) [6,33,129,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9636
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9637 : Route 9 := (fun mask => (mask,id))

def c9637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9637 : Upper (D 6) (R 6) [6,33,129,80,260,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,260,64] 13 (by decide) (choices 1) [2,8,32] r9637 c9637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1070
  · exact u1071
  · exact u1072

def b9638 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 88 280 34 100 228 356), lower := (rows 7 35 133 88 280 34 64 128 256), losses := [] }

theorem u9638 : Upper (D 6) (R 6) [6,33,129,80,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9638
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9639 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 88 280 36 98 226 354), lower := (rows 7 35 133 88 280 36 64 128 256), losses := [] }

theorem u9639 : Upper (D 6) (R 6) [6,33,129,80,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9639
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9640 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 88 280 96 102 166 294), lower := (rows 7 35 133 88 280 96 64 128 256), losses := [] }

theorem u9640 : Upper (D 6) (R 6) [6,33,129,80,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9640
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9641 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 88 304 34 76 204 332), lower := (rows 7 35 133 88 304 34 64 128 256), losses := [] }

theorem u9641 : Upper (D 6) (R 6) [6,33,129,80,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9641
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9642 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 88 304 36 74 202 330), lower := (rows 7 35 133 88 304 36 64 128 256), losses := [] }

theorem u9642 : Upper (D 6) (R 6) [6,33,129,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9642
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9643 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 88 304 40 70 198 326), lower := (rows 7 35 133 88 304 40 64 128 256), losses := [] }

theorem u9643 : Upper (D 6) (R 6) [6,33,129,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9643
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9644 : Route 9 := (fun mask => (mask,id))

def c9644 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9644 : Upper (D 6) (R 6) [6,33,129,80,288,64] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,288,64] 13 (by decide) (choices 1) [2,4,8] r9644 c9644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1073
  · exact u1074
  · exact u1075

def b9645 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 104 274 36 88 216 344), lower := (rows 7 35 133 104 274 36 64 128 256), losses := [] }

theorem u9645 : Upper (D 6) (R 6) [6,33,129,96,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9645
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9646 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 104 274 40 84 212 340), lower := (rows 7 35 133 104 274 40 64 128 256), losses := [] }

theorem u9646 : Upper (D 6) (R 6) [6,33,129,96,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9646
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9647 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 104 274 48 76 204 332), lower := (rows 7 35 133 104 274 48 64 128 256), losses := [] }

theorem u9647 : Upper (D 6) (R 6) [6,33,129,96,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9647
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9648 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 104 274 96 92 156 284), lower := (rows 7 35 133 104 274 96 64 128 256), losses := [] }

theorem u9648 : Upper (D 6) (R 6) [6,33,129,96,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9648
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9649 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 104 276 34 88 216 344), lower := (rows 7 35 133 104 276 34 64 128 256), losses := [] }

theorem u9649 : Upper (D 6) (R 6) [6,33,129,96,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9649
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9650 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 104 276 40 82 210 338), lower := (rows 7 35 133 104 276 40 64 128 256), losses := [] }

theorem u9650 : Upper (D 6) (R 6) [6,33,129,96,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9650
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9651 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 104 276 48 74 202 330), lower := (rows 7 35 133 104 276 48 64 128 256), losses := [] }

theorem u9651 : Upper (D 6) (R 6) [6,33,129,96,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9651
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9652 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 104 276 96 90 154 282), lower := (rows 7 35 133 104 276 96 64 128 256), losses := [] }

theorem u9652 : Upper (D 6) (R 6) [6,33,129,96,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9652
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9653 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 104 280 34 84 212 340), lower := (rows 7 35 133 104 280 34 64 128 256), losses := [] }

theorem u9653 : Upper (D 6) (R 6) [6,33,129,96,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9653
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9654 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 104 280 36 82 210 338), lower := (rows 7 35 133 104 280 36 64 128 256), losses := [] }

theorem u9654 : Upper (D 6) (R 6) [6,33,129,96,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9654
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9655 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 133 104 280 48 70 198 326), lower := (rows 7 35 133 104 280 48 64 128 256), losses := [] }

theorem u9655 : Upper (D 6) (R 6) [6,33,129,96,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9655
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9656 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 133 104 280 96 86 150 278), lower := (rows 7 35 133 104 280 96 64 128 256), losses := [] }

theorem u9656 : Upper (D 6) (R 6) [6,33,129,96,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9656
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9657 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 133 104 336 34 92 156 284), lower := (rows 7 35 133 104 336 34 64 128 256), losses := [] }

theorem u9657 : Upper (D 6) (R 6) [6,33,129,96,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9657
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9658 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 344, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 133 104 336 36 90 154 282), lower := (rows 7 35 133 104 336 36 64 128 256), losses := [] }

theorem u9658 : Upper (D 6) (R 6) [6,33,129,96,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9658
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9659 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 133 104 336 40 86 150 278), lower := (rows 7 35 133 104 336 40 64 128 256), losses := [] }

theorem u9659 : Upper (D 6) (R 6) [6,33,129,96,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9659
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9659
end Delivery.IrregularNine14.P06
