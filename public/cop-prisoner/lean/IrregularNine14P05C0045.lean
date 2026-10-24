import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0010

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 168 276 34 73 137 265), lower := (rows 7 50 76 168 276 34 64 128 256), losses := [] }

theorem u2700 : Upper (D 5) (R 5) [6,48,72,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2700
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 50 76 168 276 40 67 131 259), lower := (rows 7 50 76 168 276 40 64 128 256), losses := [] }

theorem u2701 : Upper (D 5) (R 5) [6,48,72,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2701
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2702 : Route 9 := (fun mask => (mask,id))

def c2702 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2702 : Upper (D 5) (R 5) [6,48,72,160,264,1] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160,264,1] 13 (by decide) (choices 1) [1,2,4] r2702 c2702
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u603
  · exact u604
  · exact u605

def b2703 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 168 280 34 69 133 261), lower := (rows 7 50 76 168 280 34 64 128 256), losses := [] }

theorem u2703 : Upper (D 5) (R 5) [6,48,72,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2703
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2704 : Route 9 := (fun mask => (mask,id))

def c2704 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2704 : Upper (D 5) (R 5) [6,48,72,160,264,4] 13 := by
  apply FastRouting.sound _ _ [6,48,72,160,264,4] 13 (by decide) (choices 1) [1,2] r2704 c2704
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u606
  · exact u607

def b2705 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 76 392 25 33 102 166 294), lower := (rows 7 50 76 392 25 33 64 128 256), losses := [] }

theorem u2705 : Upper (D 5) (R 5) [6,48,72,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2705
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2706 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 392 25 34 101 165 293), lower := (rows 7 50 76 392 25 34 64 128 256), losses := [] }

theorem u2706 : Upper (D 5) (R 5) [6,48,72,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2706
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2707 : PairBound 9 := { available := 35, camps := [], pairs := [(1,0),(1,3)], upper := (rows 7 50 76 392 25 36 99 163 291), lower := (rows 7 50 76 392 25 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 50 108 392 58 36 64 128 256) },{ target := 3, region := (rows 1 18 4 0 16 37 81 145 273), good := (rows 487 498 100 384 499 36 64 128 256) }] }

theorem u2707 : Upper (D 5) (R 5) [6,48,72,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2707
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2708 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 50 196 41 28 33 330 394 266), lower := (rows 7 50 196 41 28 33 64 128 256), losses := [] }

theorem u2708 : Upper (D 5) (R 5) [6,48,192,33,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2708
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2709 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 452, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 196 41 28 34 329 393 265), lower := (rows 7 50 196 41 28 34 64 128 256), losses := [] }

theorem u2709 : Upper (D 5) (R 5) [6,48,192,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2709
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2710 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 453, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 196 41 28 40 323 387 259), lower := (rows 7 50 196 41 28 40 64 128 256), losses := [] }

theorem u2710 : Upper (D 5) (R 5) [6,48,192,33,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2710
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2711 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 7 50 196 41 28 288 75 139 267), lower := (rows 7 50 196 41 28 288 64 128 256), losses := [] }

theorem u2711 : Upper (D 5) (R 5) [6,48,192,33,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2711
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2712 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 196 41 273 34 76 140 268), lower := (rows 7 50 196 41 273 34 64 128 256), losses := [] }

theorem u2712 : Upper (D 5) (R 5) [6,48,192,33,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2712
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2713 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 274, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 50 196 41 273 36 74 138 266), lower := (rows 7 50 196 41 273 36 64 128 256), losses := [] }

theorem u2713 : Upper (D 5) (R 5) [6,48,192,33,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2713
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2714 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 50 196 41 273 40 78 142 270), lower := (rows 7 50 196 41 273 40 64 128 256), losses := [] }

theorem u2714 : Upper (D 5) (R 5) [6,48,192,33,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2714
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2715 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 50 196 41 276 33 74 138 266), lower := (rows 7 50 196 41 276 33 64 128 256), losses := [] }

theorem u2715 : Upper (D 5) (R 5) [6,48,192,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2715
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2716 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 196 41 276 34 73 137 265), lower := (rows 7 50 196 41 276 34 64 128 256), losses := [] }

theorem u2716 : Upper (D 5) (R 5) [6,48,192,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2716
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2717 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 7 50 196 41 276 40 75 139 267), lower := (rows 7 50 196 41 276 40 64 128 256), losses := [] }

theorem u2717 : Upper (D 5) (R 5) [6,48,192,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2717
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2718 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 50 196 41 280 33 78 142 270), lower := (rows 7 50 196 41 280 33 64 128 256), losses := [] }

theorem u2718 : Upper (D 5) (R 5) [6,48,192,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2718
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2719 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 196 41 280 34 77 141 269), lower := (rows 7 50 196 41 280 34 64 128 256), losses := [] }

theorem u2719 : Upper (D 5) (R 5) [6,48,192,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2719
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 274, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 50 196 41 280 36 75 139 267), lower := (rows 7 50 196 41 280 36 64 128 256), losses := [] }

theorem u2720 : Upper (D 5) (R 5) [6,48,192,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2720
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 196 41 280 40 71 135 263), lower := (rows 7 50 196 41 280 40 64 128 256), losses := [] }

theorem u2721 : Upper (D 5) (R 5) [6,48,192,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2721
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 50 196 44 25 33 330 394 266), lower := (rows 7 50 196 44 25 33 64 128 256), losses := [] }

theorem u2722 : Upper (D 5) (R 5) [6,48,192,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2722
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 7 50 196 44 25 34 329 393 265), lower := (rows 7 50 196 44 25 34 64 128 256), losses := [] }

theorem u2723 : Upper (D 5) (R 5) [6,48,192,36,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2723
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 453, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 196 44 25 40 323 387 259), lower := (rows 7 50 196 44 25 40 64 128 256), losses := [] }

theorem u2724 : Upper (D 5) (R 5) [6,48,192,36,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2724
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2725 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 290, targets := 4 }], pairs := [(1,2)], upper := (rows 7 50 196 44 25 288 75 139 267), lower := (rows 7 50 196 44 25 288 64 128 256), losses := [] }

theorem u2725 : Upper (D 5) (R 5) [6,48,192,36,9,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2725
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2726 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 196 44 273 33 74 138 266), lower := (rows 7 50 196 44 273 33 64 128 256), losses := [] }

theorem u2726 : Upper (D 5) (R 5) [6,48,192,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2726
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2727 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 44 273 34 73 137 265), lower := (rows 7 50 196 44 273 34 64 128 256), losses := [] }

theorem u2727 : Upper (D 5) (R 5) [6,48,192,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2727
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 50 196 44 273 40 75 139 267), lower := (rows 7 50 196 44 273 40 64 128 256), losses := [] }

theorem u2728 : Upper (D 5) (R 5) [6,48,192,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2728
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2729 : Route 9 := (fun mask => (mask,id))

def c2729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2729 : Upper (D 5) (R 5) [6,48,192,36,264,1] 13 := by
  apply FastRouting.sound _ _ [6,48,192,36,264,1] 13 (by decide) (choices 1) [1,2,8] r2729 c2729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u608
  · exact u609
  · exact u610

def b2730 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 44 280 34 73 137 265), lower := (rows 7 50 196 44 280 34 64 128 256), losses := [] }

theorem u2730 : Upper (D 5) (R 5) [6,48,192,36,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2730
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2731 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 196 44 280 40 67 131 259), lower := (rows 7 50 196 44 280 40 64 128 256), losses := [] }

theorem u2731 : Upper (D 5) (R 5) [6,48,192,36,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2731
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2732 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 196 265 28 33 106 170 298), lower := (rows 7 50 196 265 28 33 64 128 256), losses := [] }

theorem u2732 : Upper (D 5) (R 5) [6,48,192,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2732
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2733 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 265 28 34 105 169 297), lower := (rows 7 50 196 265 28 34 64 128 256), losses := [] }

theorem u2733 : Upper (D 5) (R 5) [6,48,192,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2733
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2734 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 196 265 28 40 99 163 291), lower := (rows 7 50 196 265 28 40 64 128 256), losses := [] }

theorem u2734 : Upper (D 5) (R 5) [6,48,192,257,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2734
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2735 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 196 266 25 33 108 172 300), lower := (rows 7 50 196 266 25 33 64 128 256), losses := [] }

theorem u2735 : Upper (D 5) (R 5) [6,48,192,258,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2735
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 228, targets := 2 }], pairs := [(1,0),(2,1)], upper := (rows 7 50 196 266 25 36 105 169 297), lower := (rows 7 50 196 266 25 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 50 228 266 58 36 64 128 256) }] }

theorem u2736 : Upper (D 5) (R 5) [6,48,192,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2736
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 196 266 25 40 101 165 293), lower := (rows 7 50 196 266 25 40 64 128 256), losses := [] }

theorem u2737 : Upper (D 5) (R 5) [6,48,192,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2737
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2738 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 196 266 28 33 105 169 297), lower := (rows 7 50 196 266 28 33 64 128 256), losses := [] }

theorem u2738 : Upper (D 5) (R 5) [6,48,192,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2738
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2739 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 196 266 28 40 97 161 289), lower := (rows 7 50 196 266 28 40 64 128 256), losses := [] }

theorem u2739 : Upper (D 5) (R 5) [6,48,192,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2739
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2740 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 196 268 25 33 106 170 298), lower := (rows 7 50 196 268 25 33 64 128 256), losses := [] }

theorem u2740 : Upper (D 5) (R 5) [6,48,192,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2740
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 7 50 196 268 25 34 105 169 297), lower := (rows 7 50 196 268 25 34 64 128 256), losses := [] }

theorem u2741 : Upper (D 5) (R 5) [6,48,192,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2741
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 196 268 25 40 99 163 291), lower := (rows 7 50 196 268 25 40 64 128 256), losses := [] }

theorem u2742 : Upper (D 5) (R 5) [6,48,192,260,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2742
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2743 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 196 296 25 33 78 142 270), lower := (rows 7 50 196 296 25 33 64 128 256), losses := [] }

theorem u2743 : Upper (D 5) (R 5) [6,48,192,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2743
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2744 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 296 25 34 77 141 269), lower := (rows 7 50 196 296 25 34 64 128 256), losses := [] }

theorem u2744 : Upper (D 5) (R 5) [6,48,192,288,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2744
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2745 : PairBound 9 := { available := 11, camps := [], pairs := [(1,0),(1,3)], upper := (rows 7 50 196 296 25 36 75 139 267), lower := (rows 7 50 196 296 25 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 50 228 296 58 36 64 128 256) },{ target := 3, region := (rows 1 18 4 0 16 37 64 128 256), good := (rows 39 50 228 288 51 36 64 128 256) }] }

theorem u2745 : Upper (D 5) (R 5) [6,48,192,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2745
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2746 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 197, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 196 296 25 40 71 135 263), lower := (rows 7 50 196 296 25 40 64 128 256), losses := [] }

theorem u2746 : Upper (D 5) (R 5) [6,48,192,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2746
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2747 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 196 296 28 33 75 139 267), lower := (rows 7 50 196 296 28 33 64 128 256), losses := [] }

theorem u2747 : Upper (D 5) (R 5) [6,48,192,288,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2747
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 196 296 28 34 73 137 265), lower := (rows 7 50 196 296 28 34 64 128 256), losses := [] }

theorem u2748 : Upper (D 5) (R 5) [6,48,192,288,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2748
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 196 296 28 40 67 131 259), lower := (rows 7 50 196 296 28 40 64 128 256), losses := [] }

theorem u2749 : Upper (D 5) (R 5) [6,48,192,288,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2749
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 48, targets := 1 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,0),(4,3)], upper := (rows 7 67 140 25 52 34 360 424 296), lower := (rows 7 67 140 25 52 34 64 128 256), losses := [] }

theorem u2750 : Upper (D 5) (R 5) [6,65,136,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2750
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 140 25 52 40 354 418 290), lower := (rows 7 67 140 25 52 40 64 128 256), losses := [] }

theorem u2751 : Upper (D 5) (R 5) [6,65,136,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2751
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 354, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 140 25 52 288 106 170 298), lower := (rows 7 67 140 25 52 288 64 128 256), losses := [] }

theorem u2752 : Upper (D 5) (R 5) [6,65,136,17,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2752
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2753 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 67 140 25 276 34 104 168 296), lower := (rows 7 67 140 25 276 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 28 35 72 136 264), good := (rows 54 98 476 508 276 34 64 128 256) }] }

theorem u2753 : Upper (D 5) (R 5) [6,65,136,17,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2753
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2754 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 67 140 25 276 40 98 162 290), lower := (rows 7 67 140 25 276 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 44 65 129 257), good := (rows 502 466 188 508 308 60 64 128 256) }] }

theorem u2754 : Upper (D 5) (R 5) [6,65,136,17,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2754
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2755 : PairBound 9 := { available := 44, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 67 140 25 304 34 108 172 300), lower := (rows 7 67 140 25 304 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 35 72 136 264), good := (rows 38 98 476 508 304 34 64 128 256) }] }

theorem u2755 : Upper (D 5) (R 5) [6,65,136,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2755
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2756 : Route 9 := (fun mask => (mask,id))

def c2756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2756 : Upper (D 5) (R 5) [6,65,136,17,288,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,17,288,4] 13 (by decide) (choices 1) [2,8,32] r2756 c2756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u611
  · exact u612
  · exact u613

def b2757 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0),(4,0)], upper := (rows 7 67 140 25 304 40 102 166 294), lower := (rows 7 67 140 25 304 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 44 65 129 257), good := (rows 502 466 188 508 304 60 64 128 256) }] }

theorem u2757 : Upper (D 5) (R 5) [6,65,136,17,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2757
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2758 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 26 52 33 360 424 296), lower := (rows 7 67 140 26 52 33 64 128 256), losses := [] }

theorem u2758 : Upper (D 5) (R 5) [6,65,136,18,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2758
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2759 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 140 26 52 40 353 417 289), lower := (rows 7 67 140 26 52 40 64 128 256), losses := [] }

theorem u2759 : Upper (D 5) (R 5) [6,65,136,18,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2759
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P05
