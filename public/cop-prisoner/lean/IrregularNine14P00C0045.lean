import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0025
import IrregularNine14P00C0026

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 56 217 233 201 201 457), lower := (rows 51 262 69 56 16 32 64 128 256), losses := [] }

theorem u2700 : Upper (D 0) (R 0) [50,260,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2700
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 262 69 73 184 184 248 184 440), lower := (rows 51 262 69 73 16 32 64 128 256), losses := [] }

theorem u2701 : Upper (D 0) (R 0) [50,260,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2701
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2702 : Route 9 := (fun mask => (mask,id))

def c2702 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2702 : Upper (D 0) (R 0) [50,260,65,80] 13 := by
  apply FastRouting.sound _ _ [50,260,65,80] 13 (by decide) (choices 1) [1,8,32,128] r2702 c2702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1506
  · exact u1507
  · exact u1508
  · exact u1509

def r2703 : Route 9 := (fun mask => (mask,id))

def c2703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2703 : Upper (D 0) (R 0) [50,260,65,129] 13 := by
  apply FastRouting.sound _ _ [50,260,65,129] 13 (by decide) (choices 1) [8,32,64,128] r2703 c2703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1510
  · exact u1511
  · exact u1512
  · exact u1513

def r2704 : Route 9 := (fun mask => (mask,id))

def c2704 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2704 : Upper (D 0) (R 0) [50,260,65,144] 13 := by
  apply FastRouting.sound _ _ [50,260,65,144] 13 (by decide) (choices 1) [1,8,32,64,128] r2704 c2704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1514
  · exact u1515
  · exact u1516
  · exact u1517
  · exact u1518

def r2705 : Route 9 := (fun mask => (mask,id))

def c2705 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2705 : Upper (D 0) (R 0) [50,260,65,192] 13 := by
  apply FastRouting.sound _ _ [50,260,65,192] 13 (by decide) (choices 1) [1,8,32,128] r2705 c2705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1519
  · exact u1520
  · exact u1521
  · exact u1522

def b2706 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 76 25 241 225 225 225 481), lower := (rows 51 262 76 25 16 32 64 128 256), losses := [] }

theorem u2706 : Upper (D 0) (R 0) [50,260,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2706
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2707 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 76 56 209 225 193 193 449), lower := (rows 51 262 76 56 16 32 64 128 256), losses := [] }

theorem u2707 : Upper (D 0) (R 0) [50,260,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2707
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 262 76 73 177 177 241 177 433), lower := (rows 51 262 76 73 16 32 64 128 256), losses := [] }

theorem u2708 : Upper (D 0) (R 0) [50,260,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2708
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2709 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 262 76 88 177 161 225 161 417), lower := (rows 51 262 76 88 16 32 64 128 256), losses := [] }

theorem u2709 : Upper (D 0) (R 0) [50,260,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2709
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2710 : Route 9 := (fun mask => (mask,id))

def c2710 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2710 : Upper (D 0) (R 0) [50,260,72,129] 13 := by
  apply FastRouting.sound _ _ [50,260,72,129] 13 (by decide) (choices 1) [1,32,64,128] r2710 c2710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1523
  · exact u1524
  · exact u1525
  · exact u1526

def r2711 : Route 9 := (fun mask => (mask,id))

def c2711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2711 : Upper (D 0) (R 0) [50,260,72,144] 13 := by
  apply FastRouting.sound _ _ [50,260,72,144] 13 (by decide) (choices 1) [1,32,64,128] r2711 c2711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1527
  · exact u1528
  · exact u1529
  · exact u1530

def b2712 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 262 76 200 177 177 241 177 433), lower := (rows 51 262 76 200 16 32 64 128 256), losses := [] }

theorem u2712 : Upper (D 0) (R 0) [50,260,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2712
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2713 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 51 262 196 25 249 233 233 233 489), lower := (rows 51 262 196 25 16 32 64 128 256), losses := [] }

theorem u2713 : Upper (D 0) (R 0) [50,260,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2713
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 196 56 217 233 201 201 457), lower := (rows 51 262 196 56 16 32 64 128 256), losses := [] }

theorem u2714 : Upper (D 0) (R 0) [50,260,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2714
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2715 : Route 9 := (fun mask => (mask,id))

def c2715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2715 : Upper (D 0) (R 0) [50,260,192,65] 13 := by
  apply FastRouting.sound _ _ [50,260,192,65] 13 (by decide) (choices 1) [1,8,32,128] r2715 c2715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1531
  · exact u1532
  · exact u1533
  · exact u1534

def r2716 : Route 9 := (fun mask => (mask,id))

def c2716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2716 : Upper (D 0) (R 0) [50,260,192,80] 13 := by
  apply FastRouting.sound _ _ [50,260,192,80] 13 (by decide) (choices 1) [1,8,32,128] r2716 c2716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1535
  · exact u1536
  · exact u1537
  · exact u1538

def b2717 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 196 200 57 57 121 185 313), lower := (rows 51 262 196 200 16 32 64 128 256), losses := [] }

theorem u2717 : Upper (D 0) (R 0) [50,260,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2717
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2718 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 13 13 240 240 240 240 496), lower := (rows 51 322 13 13 16 32 64 128 256), losses := [] }

theorem u2718 : Upper (D 0) (R 0) [50,320,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2718
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 13 25 244 228 228 228 484), lower := (rows 51 322 13 25 16 32 64 128 256), losses := [] }

theorem u2719 : Upper (D 0) (R 0) [50,320,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2719
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 13 28 241 225 225 225 481), lower := (rows 51 322 13 28 16 32 64 128 256), losses := [] }

theorem u2720 : Upper (D 0) (R 0) [50,320,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2720
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 13 56 213 229 197 197 453), lower := (rows 51 322 13 56 16 32 64 128 256), losses := [] }

theorem u2721 : Upper (D 0) (R 0) [50,320,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2721
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 13 73 180 180 244 180 436), lower := (rows 51 322 13 73 16 32 64 128 256), losses := [] }

theorem u2722 : Upper (D 0) (R 0) [50,320,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2722
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 13 76 177 177 241 177 433), lower := (rows 51 322 13 76 16 32 64 128 256), losses := [] }

theorem u2723 : Upper (D 0) (R 0) [50,320,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2723
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 13 88 181 165 229 165 421), lower := (rows 51 322 13 88 16 32 64 128 256), losses := [] }

theorem u2724 : Upper (D 0) (R 0) [50,320,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2724
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 13 137 244 244 244 244 500), lower := (rows 51 322 13 137 16 32 64 128 256), losses := [] }

theorem u2725 : Upper (D 0) (R 0) [50,320,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2725
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2726 : Route 9 := (fun mask => (mask,id))

def c2726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2726 : Upper (D 0) (R 0) [50,320,9,132] 13 := by
  apply FastRouting.sound _ _ [50,320,9,132] 13 (by decide) (choices 1) [1,32,64,128] r2726 c2726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1539
  · exact u1540
  · exact u1541
  · exact u1542

def b2727 : PairBound 9 := { available := 229, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 13 152 245 229 229 229 485), lower := (rows 51 322 13 152 16 32 64 128 256), losses := [] }

theorem u2727 : Upper (D 0) (R 0) [50,320,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2727
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2728 : Route 9 := (fun mask => (mask,id))

def c2728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2728 : Upper (D 0) (R 0) [50,320,9,192] 13 := by
  apply FastRouting.sound _ _ [50,320,9,192] 13 (by decide) (choices 1) [1,4,32,128] r2728 c2728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1543
  · exact u1544
  · exact u1545
  · exact u1546

def b2729 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 21 44 217 233 201 201 457), lower := (rows 51 322 21 44 16 32 64 128 256), losses := [] }

theorem u2729 : Upper (D 0) (R 0) [50,320,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2729
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 21 76 185 169 233 169 425), lower := (rows 51 322 21 76 16 32 64 128 256), losses := [] }

theorem u2730 : Upper (D 0) (R 0) [50,320,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2730
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 21 104 157 173 205 141 397), lower := (rows 51 322 21 104 16 32 64 128 256), losses := [] }

theorem u2731 : Upper (D 0) (R 0) [50,320,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2731
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 21 137 252 236 236 236 492), lower := (rows 51 322 21 137 16 32 64 128 256), losses := [] }

theorem u2732 : Upper (D 0) (R 0) [50,320,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2732
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 21 140 249 233 233 233 489), lower := (rows 51 322 21 140 16 32 64 128 256), losses := [] }

theorem u2733 : Upper (D 0) (R 0) [50,320,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2733
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 21 168 221 237 205 205 461), lower := (rows 51 322 21 168 16 32 64 128 256), losses := [] }

theorem u2734 : Upper (D 0) (R 0) [50,320,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2734
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 173, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 21 200 189 173 237 173 429), lower := (rows 51 322 21 200 16 32 64 128 256), losses := [] }

theorem u2735 : Upper (D 0) (R 0) [50,320,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2735
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 44 209 225 193 193 449), lower := (rows 51 322 28 44 16 32 64 128 256), losses := [] }

theorem u2736 : Upper (D 0) (R 0) [50,320,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2736
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 73 181 165 229 165 421), lower := (rows 51 322 28 73 16 32 64 128 256), losses := [] }

theorem u2737 : Upper (D 0) (R 0) [50,320,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2737
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 28 76 177 161 225 161 417), lower := (rows 51 322 28 76 16 32 64 128 256), losses := [] }

theorem u2738 : Upper (D 0) (R 0) [50,320,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2738
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2739 : Route 9 := (fun mask => (mask,id))

def c2739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2739 : Upper (D 0) (R 0) [50,320,24,96] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96] 13 (by decide) (choices 1) [1,4,128] r2739 c2739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1547
  · exact u1548
  · exact u1549

def r2740 : Route 9 := (fun mask => (mask,id))

def c2740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2740 : Upper (D 0) (R 0) [50,320,24,129] 13 := by
  apply FastRouting.sound _ _ [50,320,24,129] 13 (by decide) (choices 1) [1,4,32,64,128] r2740 c2740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1550
  · exact u1551
  · exact u1552
  · exact u1553
  · exact u1554

def b2741 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 28 140 241 225 225 225 481), lower := (rows 51 322 28 140 16 32 64 128 256), losses := [] }

theorem u2741 : Upper (D 0) (R 0) [50,320,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2741
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2742 : Route 9 := (fun mask => (mask,id))

def c2742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2742 : Upper (D 0) (R 0) [50,320,24,160] 13 := by
  apply FastRouting.sound _ _ [50,320,24,160] 13 (by decide) (choices 1) [1,4,64,128] r2742 c2742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1555
  · exact u1556
  · exact u1557
  · exact u1558

def r2743 : Route 9 := (fun mask => (mask,id))

def c2743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2743 : Upper (D 0) (R 0) [50,320,24,192] 13 := by
  apply FastRouting.sound _ _ [50,320,24,192] 13 (by decide) (choices 1) [1,4,32,128] r2743 c2743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1559
  · exact u1560
  · exact u1561
  · exact u1562

def b2744 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 52 76 153 169 201 137 393), lower := (rows 51 322 52 76 16 32 64 128 256), losses := [] }

theorem u2744 : Upper (D 0) (R 0) [50,320,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2744
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 52 137 221 237 205 205 461), lower := (rows 51 322 52 137 16 32 64 128 256), losses := [] }

theorem u2745 : Upper (D 0) (R 0) [50,320,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2745
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 52 140 217 233 201 201 457), lower := (rows 51 322 52 140 16 32 64 128 256), losses := [] }

theorem u2746 : Upper (D 0) (R 0) [50,320,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2746
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 52 200 157 173 205 141 397), lower := (rows 51 322 52 200 16 32 64 128 256), losses := [] }

theorem u2747 : Upper (D 0) (R 0) [50,320,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2747
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 188, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 51 322 69 137 188 188 252 188 444), lower := (rows 51 322 69 137 16 32 64 128 256), losses := [] }

theorem u2748 : Upper (D 0) (R 0) [50,320,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2748
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 51 322 69 140 185 185 249 185 441), lower := (rows 51 322 69 140 16 32 64 128 256), losses := [] }

theorem u2749 : Upper (D 0) (R 0) [50,320,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2749
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 173, camps := [{ cop := 2, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 51 322 69 152 189 173 237 173 429), lower := (rows 51 322 69 152 16 32 64 128 256), losses := [] }

theorem u2750 : Upper (D 0) (R 0) [50,320,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2750
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2751 : Route 9 := (fun mask => (mask,id))

def c2751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2751 : Upper (D 0) (R 0) [50,320,72,129] 13 := by
  apply FastRouting.sound _ _ [50,320,72,129] 13 (by decide) (choices 1) [1,4,32,128] r2751 c2751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1563
  · exact u1564
  · exact u1565
  · exact u1566

def b2752 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 76 140 177 177 241 177 433), lower := (rows 51 322 76 140 16 32 64 128 256), losses := [] }

theorem u2752 : Upper (D 0) (R 0) [50,320,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2752
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2753 : Route 9 := (fun mask => (mask,id))

def c2753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2753 : Upper (D 0) (R 0) [50,320,72,144] 13 := by
  apply FastRouting.sound _ _ [50,320,72,144] 13 (by decide) (choices 1) [1,4,32,128] r2753 c2753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1567
  · exact u1568
  · exact u1569
  · exact u1570

def r2754 : Route 9 := (fun mask => (mask,id))

def c2754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2754 : Upper (D 0) (R 0) [50,320,80,129] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129] 13 (by decide) (choices 1) [1,4,8,32,128] r2754 c2754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1571
  · exact u1572
  · exact u1573
  · exact u1574
  · exact u1575

def r2755 : Route 9 := (fun mask => (mask,id))

def c2755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2755 : Upper (D 0) (R 0) [50,320,80,132] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132] 13 (by decide) (choices 1) [1,8,32,128] r2755 c2755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1576
  · exact u1577
  · exact u1578
  · exact u1579

def r2756 : Route 9 := (fun mask => (mask,id))

def c2756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2756 : Upper (D 0) (R 0) [50,320,80,160] 13 := by
  apply FastRouting.sound _ _ [50,320,80,160] 13 (by decide) (choices 1) [1,4,8,128] r2756 c2756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1580
  · exact u1581
  · exact u1582
  · exact u1583

def b2757 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 322 133 137 124 124 124 252 380), lower := (rows 51 322 133 137 16 32 64 128 256), losses := [] }

theorem u2757 : Upper (D 0) (R 0) [50,320,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2757
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2758 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 51 322 133 140 121 121 121 249 377), lower := (rows 51 322 133 140 16 32 64 128 256), losses := [] }

theorem u2758 : Upper (D 0) (R 0) [50,320,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2758
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2759 : Route 9 := (fun mask => (mask,id))

def c2759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2759 : Upper (D 0) (R 0) [50,320,129,144] 13 := by
  apply FastRouting.sound _ _ [50,320,129,144] 13 (by decide) (choices 1) [1,4,8,32,64] r2759 c2759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1584
  · exact u1585
  · exact u1586
  · exact u1587
  · exact u1588

#print axioms u2759
end Delivery.IrregularNine14.P00
