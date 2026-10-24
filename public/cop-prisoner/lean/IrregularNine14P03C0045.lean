import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0012
import IrregularNine14P03C0013

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2700 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 25 81 416 480 416 416), lower := (rows 35 7 76 25 81 32 64 128 256), losses := [] }

theorem u2700 : Upper (D 3) (R 3) [34,5,72,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2700
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2701 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 25 112 417 449 385 385), lower := (rows 35 7 76 25 112 32 64 128 256), losses := [] }

theorem u2701 : Upper (D 3) (R 3) [34,5,72,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2701
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2702 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 76 25 145 480 480 480 480), lower := (rows 35 7 76 25 145 32 64 128 256), losses := [] }

theorem u2702 : Upper (D 3) (R 3) [34,5,72,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2702
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2703 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 25 176 481 449 449 449), lower := (rows 35 7 76 25 176 32 64 128 256), losses := [] }

theorem u2703 : Upper (D 3) (R 3) [34,5,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2703
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2704 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 25 208 417 481 417 417), lower := (rows 35 7 76 25 208 32 64 128 256), losses := [] }

theorem u2704 : Upper (D 3) (R 3) [34,5,72,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2704
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2705 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 76 25 273 224 224 224 480), lower := (rows 35 7 76 25 273 32 64 128 256), losses := [] }

theorem u2705 : Upper (D 3) (R 3) [34,5,72,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2705
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2706 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 25 304 225 193 193 449), lower := (rows 35 7 76 25 304 32 64 128 256), losses := [] }

theorem u2706 : Upper (D 3) (R 3) [34,5,72,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2706
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2707 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 25 336 161 225 161 417), lower := (rows 35 7 76 25 336 32 64 128 256), losses := [] }

theorem u2707 : Upper (D 3) (R 3) [34,5,72,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2707
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2708 : Route 9 := (fun mask => (mask,id))

def c2708 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2708 : Upper (D 3) (R 3) [34,5,72,17,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,17,384] 13 (by decide) (choices 1) [1,64,128] r2708 c2708
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u737
  · exact u738
  · exact u739

def b2709 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 137 49 496 464 464 464), lower := (rows 35 7 76 137 49 32 64 128 256), losses := [] }

theorem u2709 : Upper (D 3) (R 3) [34,5,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2709
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2710 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 137 81 432 496 432 432), lower := (rows 35 7 76 137 81 32 64 128 256), losses := [] }

theorem u2710 : Upper (D 3) (R 3) [34,5,72,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2710
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2711 : Route 9 := (fun mask => (mask,id))

def c2711 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2711 : Upper (D 3) (R 3) [34,5,72,129,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,96] 13 (by decide) (choices 1) [1,16,128,256] r2711 c2711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u740
  · exact u741
  · exact u742
  · exact u743

def b2712 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 76 137 145 368 368 496 368), lower := (rows 35 7 76 137 145 32 64 128 256), losses := [] }

theorem u2712 : Upper (D 3) (R 3) [34,5,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2712
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2713 : Route 9 := (fun mask => (mask,id))

def c2713 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2713 : Upper (D 3) (R 3) [34,5,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,160] 13 (by decide) (choices 1) [1,16,64,256] r2713 c2713
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u744
  · exact u745
  · exact u746
  · exact u747

def r2714 : Route 9 := (fun mask => (mask,id))

def c2714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2714 : Upper (D 3) (R 3) [34,5,72,129,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,192] 13 (by decide) (choices 1) [1,16,256] r2714 c2714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u748
  · exact u749
  · exact u750

def r2715 : Route 9 := (fun mask => (mask,id))

def c2715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2715 : Upper (D 3) (R 3) [34,5,72,129,257] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,257] 13 (by decide) (choices 1) [16,64,128] r2715 c2715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u751
  · exact u752
  · exact u753

def r2716 : Route 9 := (fun mask => (mask,id))

def c2716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2716 : Upper (D 3) (R 3) [34,5,72,129,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,288] 13 (by decide) (choices 1) [1,16,64,128] r2716 c2716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u754
  · exact u755
  · exact u756
  · exact u757

def r2717 : Route 9 := (fun mask => (mask,id))

def c2717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2717 : Upper (D 3) (R 3) [34,5,72,129,320] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,320] 13 (by decide) (choices 1) [1,16,128] r2717 c2717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u758
  · exact u759
  · exact u760

def r2718 : Route 9 := (fun mask => (mask,id))

def c2718 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2718 : Upper (D 3) (R 3) [34,5,72,129,384] 13 := by
  apply FastRouting.sound _ _ [34,5,72,129,384] 13 (by decide) (choices 1) [1,16,64] r2718 c2718
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u761
  · exact u762
  · exact u763

def b2719 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 152 49 481 449 449 449), lower := (rows 35 7 76 152 49 32 64 128 256), losses := [] }

theorem u2719 : Upper (D 3) (R 3) [34,5,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2719
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2720 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 81 417 481 417 417), lower := (rows 35 7 76 152 81 32 64 128 256), losses := [] }

theorem u2720 : Upper (D 3) (R 3) [34,5,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2720
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2721 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 112 417 449 385 385), lower := (rows 35 7 76 152 112 32 64 128 256), losses := [] }

theorem u2721 : Upper (D 3) (R 3) [34,5,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2721
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2722 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 152 145 353 353 481 353), lower := (rows 35 7 76 152 145 32 64 128 256), losses := [] }

theorem u2722 : Upper (D 3) (R 3) [34,5,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2722
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2723 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 152 176 353 321 449 321), lower := (rows 35 7 76 152 176 32 64 128 256), losses := [] }

theorem u2723 : Upper (D 3) (R 3) [34,5,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2723
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2724 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 152 208 289 353 417 289), lower := (rows 35 7 76 152 208 32 64 128 256), losses := [] }

theorem u2724 : Upper (D 3) (R 3) [34,5,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2724
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2725 : Route 9 := (fun mask => (mask,id))

def c2725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2725 : Upper (D 3) (R 3) [34,5,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,257] 13 (by decide) (choices 1) [1,64,128] r2725 c2725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u764
  · exact u765
  · exact u766

def r2726 : Route 9 := (fun mask => (mask,id))

def c2726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2726 : Upper (D 3) (R 3) [34,5,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,5,72,144,288] 13 (by decide) (choices 1) [1,64,128] r2726 c2726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u767
  · exact u768
  · exact u769

def b2727 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 336 161 225 161 417), lower := (rows 35 7 76 152 336 32 64 128 256), losses := [] }

theorem u2727 : Upper (D 3) (R 3) [34,5,72,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2727
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2728 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 152 400 97 97 225 353), lower := (rows 35 7 76 152 400 32 64 128 256), losses := [] }

theorem u2728 : Upper (D 3) (R 3) [34,5,72,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2728
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2729 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 265 49 240 208 208 464), lower := (rows 35 7 76 265 49 32 64 128 256), losses := [] }

theorem u2729 : Upper (D 3) (R 3) [34,5,72,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2729
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2730 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 265 81 176 240 176 432), lower := (rows 35 7 76 265 81 32 64 128 256), losses := [] }

theorem u2730 : Upper (D 3) (R 3) [34,5,72,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2730
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2731 : Route 9 := (fun mask => (mask,id))

def c2731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2731 : Upper (D 3) (R 3) [34,5,72,257,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,96] 13 (by decide) (choices 1) [1,16,128] r2731 c2731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u770
  · exact u771
  · exact u772

def r2732 : Route 9 := (fun mask => (mask,id))

def c2732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2732 : Upper (D 3) (R 3) [34,5,72,257,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,129] 13 (by decide) (choices 1) [16,64,128] r2732 c2732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u773
  · exact u774
  · exact u775

def r2733 : Route 9 := (fun mask => (mask,id))

def c2733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2733 : Upper (D 3) (R 3) [34,5,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,160] 13 (by decide) (choices 1) [1,16,64,128] r2733 c2733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u776
  · exact u777
  · exact u778
  · exact u779

def r2734 : Route 9 := (fun mask => (mask,id))

def c2734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2734 : Upper (D 3) (R 3) [34,5,72,257,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,192] 13 (by decide) (choices 1) [1,16,128] r2734 c2734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u780
  · exact u781
  · exact u782

def b2735 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 280 49 225 193 193 449), lower := (rows 35 7 76 280 49 32 64 128 256), losses := [] }

theorem u2735 : Upper (D 3) (R 3) [34,5,72,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2735
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2736 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 81 161 225 161 417), lower := (rows 35 7 76 280 81 32 64 128 256), losses := [] }

theorem u2736 : Upper (D 3) (R 3) [34,5,72,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2736
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2737 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 112 161 193 129 385), lower := (rows 35 7 76 280 112 32 64 128 256), losses := [] }

theorem u2737 : Upper (D 3) (R 3) [34,5,72,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2737
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2738 : Route 9 := (fun mask => (mask,id))

def c2738 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2738 : Upper (D 3) (R 3) [34,5,72,272,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,272,129] 13 (by decide) (choices 1) [1,64,128] r2738 c2738
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u783
  · exact u784
  · exact u785

def r2739 : Route 9 := (fun mask => (mask,id))

def c2739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2739 : Upper (D 3) (R 3) [34,5,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,272,160] 13 (by decide) (choices 1) [1,64,128] r2739 c2739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u786
  · exact u787
  · exact u788

def b2740 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 208 161 225 161 417), lower := (rows 35 7 76 280 208 32 64 128 256), losses := [] }

theorem u2740 : Upper (D 3) (R 3) [34,5,72,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2740
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2741 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 76 392 49 241 209 209 465), lower := (rows 35 7 76 392 49 32 64 128 256), losses := [] }

theorem u2741 : Upper (D 3) (R 3) [34,5,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2741
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2742 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 392 81 177 241 177 433), lower := (rows 35 7 76 392 81 32 64 128 256), losses := [] }

theorem u2742 : Upper (D 3) (R 3) [34,5,72,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2742
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2743 : Route 9 := (fun mask => (mask,id))

def c2743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2743 : Upper (D 3) (R 3) [34,5,72,384,96] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,96] 13 (by decide) (choices 1) [1,16,128] r2743 c2743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u789
  · exact u790
  · exact u791

def r2744 : Route 9 := (fun mask => (mask,id))

def c2744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2744 : Upper (D 3) (R 3) [34,5,72,384,129] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,129] 13 (by decide) (choices 1) [1,16,64] r2744 c2744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u792
  · exact u793
  · exact u794

def r2745 : Route 9 := (fun mask => (mask,id))

def c2745 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2745 : Upper (D 3) (R 3) [34,5,72,384,160] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,160] 13 (by decide) (choices 1) [1,16,64] r2745 c2745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u795
  · exact u796
  · exact u797

def r2746 : Route 9 := (fun mask => (mask,id))

def c2746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2746 : Upper (D 3) (R 3) [34,5,72,384,192] 13 := by
  apply FastRouting.sound _ _ [34,5,72,384,192] 13 (by decide) (choices 1) [1,16] r2746 c2746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u798
  · exact u799

def b2747 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 196 25 25 480 480 480 480), lower := (rows 35 7 196 25 25 32 64 128 256), losses := [] }

theorem u2747 : Upper (D 3) (R 3) [34,5,192,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2747
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2748 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 25 49 488 456 456 456), lower := (rows 35 7 196 25 49 32 64 128 256), losses := [] }

theorem u2748 : Upper (D 3) (R 3) [34,5,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2748
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2749 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 25 56 481 449 449 449), lower := (rows 35 7 196 25 56 32 64 128 256), losses := [] }

theorem u2749 : Upper (D 3) (R 3) [34,5,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2749
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2750 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 196 25 81 424 488 424 424), lower := (rows 35 7 196 25 81 32 64 128 256), losses := [] }

theorem u2750 : Upper (D 3) (R 3) [34,5,192,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2750
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2751 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 25 88 417 481 417 417), lower := (rows 35 7 196 25 88 32 64 128 256), losses := [] }

theorem u2751 : Upper (D 3) (R 3) [34,5,192,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2751
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2752 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 25 112 425 457 393 393), lower := (rows 35 7 196 25 112 32 64 128 256), losses := [] }

theorem u2752 : Upper (D 3) (R 3) [34,5,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2752
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2753 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 196 25 208 297 361 425 297), lower := (rows 35 7 196 25 208 32 64 128 256), losses := [] }

theorem u2753 : Upper (D 3) (R 3) [34,5,192,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2753
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2754 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 196 25 273 232 232 232 488), lower := (rows 35 7 196 25 273 32 64 128 256), losses := [] }

theorem u2754 : Upper (D 3) (R 3) [34,5,192,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2754
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2755 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2755 : Upper (D 3) (R 3) [34,5,192,17,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,264] 13 (by decide) (choices 1) [1,64] r2755 c2755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u800
  · exact u801

def b2756 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 25 304 233 201 201 457), lower := (rows 35 7 196 25 304 32 64 128 256), losses := [] }

theorem u2756 : Upper (D 3) (R 3) [34,5,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2756
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2757 : Route 9 := (fun mask => (mask,id))

def c2757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2757 : Upper (D 3) (R 3) [34,5,192,17,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,17,320] 13 (by decide) (choices 1) [1,8,128] r2757 c2757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u802
  · exact u803
  · exact u804

def b2758 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 41 88 433 465 401 401), lower := (rows 35 7 196 41 88 32 64 128 256), losses := [] }

theorem u2758 : Upper (D 3) (R 3) [34,5,192,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2758
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2759 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 41 273 248 216 216 472), lower := (rows 35 7 196 41 273 32 64 128 256), losses := [] }

theorem u2759 : Upper (D 3) (R 3) [34,5,192,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2759
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2759
end Delivery.IrregularNine14.P03
