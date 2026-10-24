import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0043

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9780 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 88 148 161 225 161 417), lower := (rows 35 322 13 88 148 32 64 128 256), losses := [] }

theorem u9780 : Upper (D 8) (R 8) [34,320,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9781 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 88 176 165 229 165 421), lower := (rows 35 322 13 88 176 32 64 128 256), losses := [] }

theorem u9781 : Upper (D 8) (R 8) [34,320,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9782 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 104 52 177 209 145 401), lower := (rows 35 322 13 104 52 32 64 128 256), losses := [] }

theorem u9782 : Upper (D 8) (R 8) [34,320,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9783 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 104 145 180 244 180 436), lower := (rows 35 322 13 104 145 32 64 128 256), losses := [] }

theorem u9783 : Upper (D 8) (R 8) [34,320,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9784 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 104 148 177 241 177 433), lower := (rows 35 322 13 104 148 32 64 128 256), losses := [] }

theorem u9784 : Upper (D 8) (R 8) [34,320,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9785 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 104 176 181 213 149 405), lower := (rows 35 322 13 104 176 32 64 128 256), losses := [] }

theorem u9785 : Upper (D 8) (R 8) [34,320,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9786 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 52 240 240 240 496), lower := (rows 35 322 13 137 52 32 64 128 256), losses := [] }

theorem u9786 : Upper (D 8) (R 8) [34,320,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9787 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 84 176 240 176 432), lower := (rows 35 322 13 137 84 32 64 128 256), losses := [] }

theorem u9787 : Upper (D 8) (R 8) [34,320,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9788 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 112 180 244 180 436), lower := (rows 35 322 13 137 112 32 64 128 256), losses := [] }

theorem u9788 : Upper (D 8) (R 8) [34,320,9,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9789 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 148 112 112 240 368), lower := (rows 35 322 13 137 148 32 64 128 256), losses := [] }

theorem u9789 : Upper (D 8) (R 8) [34,320,9,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9790 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 176 116 116 244 372), lower := (rows 35 322 13 137 176 32 64 128 256), losses := [] }

theorem u9790 : Upper (D 8) (R 8) [34,320,9,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9791 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 137 208 52 116 180 308), lower := (rows 35 322 13 137 208 32 64 128 256), losses := [] }

theorem u9791 : Upper (D 8) (R 8) [34,320,9,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9792 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 140 49 240 240 240 496), lower := (rows 35 322 13 140 49 32 64 128 256), losses := [] }

theorem u9792 : Upper (D 8) (R 8) [34,320,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9793 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 140 81 176 240 176 432), lower := (rows 35 322 13 140 81 32 64 128 256), losses := [] }

theorem u9793 : Upper (D 8) (R 8) [34,320,9,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9794 : Route 9 := (fun mask => (mask,id))

def c9794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9794 : Upper (D 8) (R 8) [34,320,9,132,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,132,96] 13 (by decide) (choices 1) [1,16,128] r9794 c9794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2600
  · exact u2601
  · exact u2602

def b9795 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 140 145 112 112 240 368), lower := (rows 35 322 13 140 145 32 64 128 256), losses := [] }

theorem u9795 : Upper (D 8) (R 8) [34,320,9,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9796 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 176 113 113 241 369), lower := (rows 35 322 13 140 176 32 64 128 256), losses := [] }

theorem u9796 : Upper (D 8) (R 8) [34,320,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9797 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 208 49 113 177 305), lower := (rows 35 322 13 140 208 32 64 128 256), losses := [] }

theorem u9797 : Upper (D 8) (R 8) [34,320,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9798 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 152 49 228 228 228 484), lower := (rows 35 322 13 152 49 32 64 128 256), losses := [] }

theorem u9798 : Upper (D 8) (R 8) [34,320,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9799 : Route 9 := (fun mask => (mask,id))

def c9799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9799 : Upper (D 8) (R 8) [34,320,9,144,36] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,36] 13 (by decide) (choices 1) [1,64,128] r9799 c9799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2603
  · exact u2604
  · exact u2605

def b9800 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 152 81 164 228 164 420), lower := (rows 35 322 13 152 81 32 64 128 256), losses := [] }

theorem u9800 : Upper (D 8) (R 8) [34,320,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9801 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 13 152 84 161 225 161 417), lower := (rows 35 322 13 152 84 32 64 128 256), losses := [] }

theorem u9801 : Upper (D 8) (R 8) [34,320,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9802 : Route 9 := (fun mask => (mask,id))

def c9802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9802 : Upper (D 8) (R 8) [34,320,9,144,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,144,96] 13 (by decide) (choices 1) [1,4,128] r9802 c9802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2606
  · exact u2607
  · exact u2608

def b9803 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 13 152 145 100 100 228 356), lower := (rows 35 322 13 152 145 32 64 128 256), losses := [] }

theorem u9803 : Upper (D 8) (R 8) [34,320,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9804 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 148 97 97 225 353), lower := (rows 35 322 13 152 148 32 64 128 256), losses := [] }

theorem u9804 : Upper (D 8) (R 8) [34,320,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9805 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 176 101 101 229 357), lower := (rows 35 322 13 152 176 32 64 128 256), losses := [] }

theorem u9805 : Upper (D 8) (R 8) [34,320,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9806 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 152 208 37 101 165 293), lower := (rows 35 322 13 152 208 32 64 128 256), losses := [] }

theorem u9806 : Upper (D 8) (R 8) [34,320,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9807 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 168 49 244 212 212 468), lower := (rows 35 322 13 168 49 32 64 128 256), losses := [] }

theorem u9807 : Upper (D 8) (R 8) [34,320,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9808 : Route 9 := (fun mask => (mask,id))

def c9808 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u9808 : Upper (D 8) (R 8) [34,320,9,160,36] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,36] 13 (by decide) (choices 1) [1,16,64,128] r9808 c9808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2609
  · exact u2610
  · exact u2611
  · exact u2612

def b9809 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 13 168 81 180 244 180 436), lower := (rows 35 322 13 168 81 32 64 128 256), losses := [] }

theorem u9809 : Upper (D 8) (R 8) [34,320,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9810 : Route 9 := (fun mask => (mask,id))

def c9810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9810 : Upper (D 8) (R 8) [34,320,9,160,68] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,68] 13 (by decide) (choices 1) [1,16,128] r9810 c9810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2613
  · exact u2614
  · exact u2615

def r9811 : Route 9 := (fun mask => (mask,id))

def c9811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9811 : Upper (D 8) (R 8) [34,320,9,160,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,96] 13 (by decide) (choices 1) [1,4,16,128] r9811 c9811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2616
  · exact u2617
  · exact u2618
  · exact u2619

def r9812 : Route 9 := (fun mask => (mask,id))

def c9812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9812 : Upper (D 8) (R 8) [34,320,9,160,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,129] 13 (by decide) (choices 1) [4,16,64] r9812 c9812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2620
  · exact u2621
  · exact u2622

def b9813 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 168 148 113 113 241 369), lower := (rows 35 322 13 168 148 32 64 128 256), losses := [] }

theorem u9813 : Upper (D 8) (R 8) [34,320,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9814 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 322 13 168 176 117 85 213 341), lower := (rows 35 322 13 168 176 32 64 128 256), losses := [] }

theorem u9814 : Upper (D 8) (R 8) [34,320,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9815 : Route 9 := (fun mask => (mask,id))

def c9815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9815 : Upper (D 8) (R 8) [34,320,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,160,192] 13 (by decide) (choices 1) [1,4,16] r9815 c9815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2623
  · exact u2624
  · exact u2625

def b9816 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 52 177 241 177 433), lower := (rows 35 322 13 200 52 32 64 128 256), losses := [] }

theorem u9816 : Upper (D 8) (R 8) [34,320,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9817 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 145 52 116 180 308), lower := (rows 35 322 13 200 145 32 64 128 256), losses := [] }

theorem u9817 : Upper (D 8) (R 8) [34,320,9,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9818 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 200 148 49 113 177 305), lower := (rows 35 322 13 200 148 32 64 128 256), losses := [] }

theorem u9818 : Upper (D 8) (R 8) [34,320,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9819 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 322 13 200 176 53 117 181 309), lower := (rows 35 322 13 200 176 32 64 128 256), losses := [] }

theorem u9819 : Upper (D 8) (R 8) [34,320,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9820 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 41 52 225 193 193 449), lower := (rows 35 322 28 41 52 32 64 128 256), losses := [] }

theorem u9820 : Upper (D 8) (R 8) [34,320,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9821 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 28 41 112 165 197 133 389), lower := (rows 35 322 28 41 112 32 64 128 256), losses := [] }

theorem u9821 : Upper (D 8) (R 8) [34,320,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9822 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 28 41 145 228 228 228 484), lower := (rows 35 322 28 41 145 32 64 128 256), losses := [] }

theorem u9822 : Upper (D 8) (R 8) [34,320,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9823 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 28 41 148 225 225 225 481), lower := (rows 35 322 28 41 148 32 64 128 256), losses := [] }

theorem u9823 : Upper (D 8) (R 8) [34,320,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9824 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 28 41 176 229 197 197 453), lower := (rows 35 322 28 41 176 32 64 128 256), losses := [] }

theorem u9824 : Upper (D 8) (R 8) [34,320,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9825 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 322 28 41 208 165 229 165 421), lower := (rows 35 322 28 41 208 32 64 128 256), losses := [] }

theorem u9825 : Upper (D 8) (R 8) [34,320,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9826 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 44 81 161 225 161 417), lower := (rows 35 322 28 44 81 32 64 128 256), losses := [] }

theorem u9826 : Upper (D 8) (R 8) [34,320,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9827 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 44 112 161 193 129 385), lower := (rows 35 322 28 44 112 32 64 128 256), losses := [] }

theorem u9827 : Upper (D 8) (R 8) [34,320,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9828 : Route 9 := (fun mask => (mask,id))

def c9828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9828 : Upper (D 8) (R 8) [34,320,24,36,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,36,129] 13 (by decide) (choices 1) [1,64,128] r9828 c9828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2626
  · exact u2627
  · exact u2628

def b9829 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 322 28 44 176 225 193 193 449), lower := (rows 35 322 28 44 176 32 64 128 256), losses := [] }

theorem u9829 : Upper (D 8) (R 8) [34,320,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9830 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 44 208 161 225 161 417), lower := (rows 35 322 28 44 208 32 64 128 256), losses := [] }

theorem u9830 : Upper (D 8) (R 8) [34,320,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9831 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 145 164 228 164 420), lower := (rows 35 322 28 73 145 32 64 128 256), losses := [] }

theorem u9831 : Upper (D 8) (R 8) [34,320,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9832 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 148 161 225 161 417), lower := (rows 35 322 28 73 148 32 64 128 256), losses := [] }

theorem u9832 : Upper (D 8) (R 8) [34,320,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9833 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 35 322 28 73 176 165 229 165 421), lower := (rows 35 322 28 73 176 32 64 128 256), losses := [] }

theorem u9833 : Upper (D 8) (R 8) [34,320,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9834 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 76 145 161 225 161 417), lower := (rows 35 322 28 76 145 32 64 128 256), losses := [] }

theorem u9834 : Upper (D 8) (R 8) [34,320,24,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9835 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 76 176 161 225 161 417), lower := (rows 35 322 28 76 176 32 64 128 256), losses := [] }

theorem u9835 : Upper (D 8) (R 8) [34,320,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9836 : Route 9 := (fun mask => (mask,id))

def c9836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9836 : Upper (D 8) (R 8) [34,320,24,96,129] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,129] 13 (by decide) (choices 1) [1,4,128] r9836 c9836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2629
  · exact u2630
  · exact u2631

def b9837 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 28 104 148 161 225 161 417), lower := (rows 35 322 28 104 148 32 64 128 256), losses := [] }

theorem u9837 : Upper (D 8) (R 8) [34,320,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r9838 : Route 9 := (fun mask => (mask,id))

def c9838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9838 : Upper (D 8) (R 8) [34,320,24,96,160] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,160] 13 (by decide) (choices 1) [1,4,128] r9838 c9838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2632
  · exact u2633
  · exact u2634

def b9839 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 322 28 137 145 100 100 228 356), lower := (rows 35 322 28 137 145 32 64 128 256), losses := [] }

theorem u9839 : Upper (D 8) (R 8) [34,320,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u9839
end Delivery.IrregularNine14.P08
