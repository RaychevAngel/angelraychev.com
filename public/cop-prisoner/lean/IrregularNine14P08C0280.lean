import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0101

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16800 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 13 104 176 181 213 149 405), lower := (rows 259 98 13 104 176 32 64 128 256), losses := [] }

theorem u16800 : Upper (D 8) (R 8) [258,96,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16801 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 52 240 240 240 496), lower := (rows 259 98 13 137 52 32 64 128 256), losses := [] }

theorem u16801 : Upper (D 8) (R 8) [258,96,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16802 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 84 176 240 176 432), lower := (rows 259 98 13 137 84 32 64 128 256), losses := [] }

theorem u16802 : Upper (D 8) (R 8) [258,96,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16803 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 148 112 112 240 368), lower := (rows 259 98 13 137 148 32 64 128 256), losses := [] }

theorem u16803 : Upper (D 8) (R 8) [258,96,9,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16804 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 176 116 116 244 372), lower := (rows 259 98 13 137 176 32 64 128 256), losses := [] }

theorem u16804 : Upper (D 8) (R 8) [258,96,9,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16805 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 137 208 52 116 180 308), lower := (rows 259 98 13 137 208 32 64 128 256), losses := [] }

theorem u16805 : Upper (D 8) (R 8) [258,96,9,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16806 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 140 49 240 240 240 496), lower := (rows 259 98 13 140 49 32 64 128 256), losses := [] }

theorem u16806 : Upper (D 8) (R 8) [258,96,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16807 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 140 81 176 240 176 432), lower := (rows 259 98 13 140 81 32 64 128 256), losses := [] }

theorem u16807 : Upper (D 8) (R 8) [258,96,9,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16808 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 140 112 177 241 177 433), lower := (rows 259 98 13 140 112 32 64 128 256), losses := [] }

theorem u16808 : Upper (D 8) (R 8) [258,96,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16809 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 140 145 112 112 240 368), lower := (rows 259 98 13 140 145 32 64 128 256), losses := [] }

theorem u16809 : Upper (D 8) (R 8) [258,96,9,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16810 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 140 176 113 113 241 369), lower := (rows 259 98 13 140 176 32 64 128 256), losses := [] }

theorem u16810 : Upper (D 8) (R 8) [258,96,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16811 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 140 208 49 113 177 305), lower := (rows 259 98 13 140 208 32 64 128 256), losses := [] }

theorem u16811 : Upper (D 8) (R 8) [258,96,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16812 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 152 49 228 228 228 484), lower := (rows 259 98 13 152 49 32 64 128 256), losses := [] }

theorem u16812 : Upper (D 8) (R 8) [258,96,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16813 : Route 9 := (fun mask => (mask,id))

def c16813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16813 : Upper (D 8) (R 8) [258,96,9,144,36] 13 := by
  apply FastRouting.sound _ _ [258,96,9,144,36] 13 (by decide) (choices 1) [1,64,128] r16813 c16813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6086
  · exact u6087
  · exact u6088

def b16814 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 152 81 164 228 164 420), lower := (rows 259 98 13 152 81 32 64 128 256), losses := [] }

theorem u16814 : Upper (D 8) (R 8) [258,96,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16815 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 13 152 84 161 225 161 417), lower := (rows 259 98 13 152 84 32 64 128 256), losses := [] }

theorem u16815 : Upper (D 8) (R 8) [258,96,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16816 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 152 112 165 229 165 421), lower := (rows 259 98 13 152 112 32 64 128 256), losses := [] }

theorem u16816 : Upper (D 8) (R 8) [258,96,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16817 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 13 152 145 100 100 228 356), lower := (rows 259 98 13 152 145 32 64 128 256), losses := [] }

theorem u16817 : Upper (D 8) (R 8) [258,96,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16818 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 152 148 97 97 225 353), lower := (rows 259 98 13 152 148 32 64 128 256), losses := [] }

theorem u16818 : Upper (D 8) (R 8) [258,96,9,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16819 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 152 176 101 101 229 357), lower := (rows 259 98 13 152 176 32 64 128 256), losses := [] }

theorem u16819 : Upper (D 8) (R 8) [258,96,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16820 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 152 208 37 101 165 293), lower := (rows 259 98 13 152 208 32 64 128 256), losses := [] }

theorem u16820 : Upper (D 8) (R 8) [258,96,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16821 : Route 9 := (fun mask => (mask,id))

def c16821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16821 : Upper (D 8) (R 8) [258,96,9,160,33] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160,33] 13 (by decide) (choices 1) [4,16,64,128] r16821 c16821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6089
  · exact u6090
  · exact u6091
  · exact u6092

def r16822 : Route 9 := (fun mask => (mask,id))

def c16822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u16822 : Upper (D 8) (R 8) [258,96,9,160,36] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160,36] 13 (by decide) (choices 1) [1,16,64,128] r16822 c16822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6093
  · exact u6094
  · exact u6095
  · exact u6096

def b16823 : PairBound 9 := { available := 180, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 13 168 81 180 244 180 436), lower := (rows 259 98 13 168 81 32 64 128 256), losses := [] }

theorem u16823 : Upper (D 8) (R 8) [258,96,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16824 : Route 9 := (fun mask => (mask,id))

def c16824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16824 : Upper (D 8) (R 8) [258,96,9,160,68] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160,68] 13 (by decide) (choices 1) [1,16,128] r16824 c16824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6097
  · exact u6098
  · exact u6099

def b16825 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 168 112 181 213 149 405), lower := (rows 259 98 13 168 112 32 64 128 256), losses := [] }

theorem u16825 : Upper (D 8) (R 8) [258,96,9,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16826 : Route 9 := (fun mask => (mask,id))

def c16826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16826 : Upper (D 8) (R 8) [258,96,9,160,129] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160,129] 13 (by decide) (choices 1) [4,16,64] r16826 c16826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6100
  · exact u6101
  · exact u6102

def b16827 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 168 148 113 113 241 369), lower := (rows 259 98 13 168 148 32 64 128 256), losses := [] }

theorem u16827 : Upper (D 8) (R 8) [258,96,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16828 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 13 168 176 117 85 213 341), lower := (rows 259 98 13 168 176 32 64 128 256), losses := [] }

theorem u16828 : Upper (D 8) (R 8) [258,96,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16829 : Route 9 := (fun mask => (mask,id))

def c16829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16829 : Upper (D 8) (R 8) [258,96,9,160,192] 13 := by
  apply FastRouting.sound _ _ [258,96,9,160,192] 13 (by decide) (choices 1) [1,4,16] r16829 c16829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6103
  · exact u6104
  · exact u6105

def b16830 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 200 49 180 244 180 436), lower := (rows 259 98 13 200 49 32 64 128 256), losses := [] }

theorem u16830 : Upper (D 8) (R 8) [258,96,9,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16831 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 200 52 177 241 177 433), lower := (rows 259 98 13 200 52 32 64 128 256), losses := [] }

theorem u16831 : Upper (D 8) (R 8) [258,96,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16832 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 200 145 52 116 180 308), lower := (rows 259 98 13 200 145 32 64 128 256), losses := [] }

theorem u16832 : Upper (D 8) (R 8) [258,96,9,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16833 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 200 148 49 113 177 305), lower := (rows 259 98 13 200 148 32 64 128 256), losses := [] }

theorem u16833 : Upper (D 8) (R 8) [258,96,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16834 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 98 13 200 176 53 117 181 309), lower := (rows 259 98 13 200 176 32 64 128 256), losses := [] }

theorem u16834 : Upper (D 8) (R 8) [258,96,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16835 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 41 49 228 196 196 452), lower := (rows 259 98 28 41 49 32 64 128 256), losses := [] }

theorem u16835 : Upper (D 8) (R 8) [258,96,24,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16836 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 41 52 225 193 193 449), lower := (rows 259 98 28 41 52 32 64 128 256), losses := [] }

theorem u16836 : Upper (D 8) (R 8) [258,96,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16837 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 41 81 164 228 164 420), lower := (rows 259 98 28 41 81 32 64 128 256), losses := [] }

theorem u16837 : Upper (D 8) (R 8) [258,96,24,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16838 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 41 84 161 225 161 417), lower := (rows 259 98 28 41 84 32 64 128 256), losses := [] }

theorem u16838 : Upper (D 8) (R 8) [258,96,24,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16839 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 98 28 41 112 165 197 133 389), lower := (rows 259 98 28 41 112 32 64 128 256), losses := [] }

theorem u16839 : Upper (D 8) (R 8) [258,96,24,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16840 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 28 41 145 228 228 228 484), lower := (rows 259 98 28 41 145 32 64 128 256), losses := [] }

theorem u16840 : Upper (D 8) (R 8) [258,96,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16841 : Route 9 := (fun mask => (mask,id))

def c16841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16841 : Upper (D 8) (R 8) [258,96,24,33,132] 13 := by
  apply FastRouting.sound _ _ [258,96,24,33,132] 13 (by decide) (choices 1) [1,64,128] r16841 c16841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6106
  · exact u6107
  · exact u6108

def r16842 : Route 9 := (fun mask => (mask,id))

def c16842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16842 : Upper (D 8) (R 8) [258,96,24,33,160] 13 := by
  apply FastRouting.sound _ _ [258,96,24,33,160] 13 (by decide) (choices 1) [1,4,64,128] r16842 c16842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6109
  · exact u6110
  · exact u6111
  · exact u6112

def r16843 : Route 9 := (fun mask => (mask,id))

def c16843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16843 : Upper (D 8) (R 8) [258,96,24,33,192] 13 := by
  apply FastRouting.sound _ _ [258,96,24,33,192] 13 (by decide) (choices 1) [1,4,128] r16843 c16843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6113
  · exact u6114
  · exact u6115

def b16844 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 44 81 161 225 161 417), lower := (rows 259 98 28 44 81 32 64 128 256), losses := [] }

theorem u16844 : Upper (D 8) (R 8) [258,96,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16845 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 28, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 44 112 161 193 129 385), lower := (rows 259 98 28 44 112 32 64 128 256), losses := [] }

theorem u16845 : Upper (D 8) (R 8) [258,96,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16846 : Route 9 := (fun mask => (mask,id))

def c16846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16846 : Upper (D 8) (R 8) [258,96,24,36,129] 13 := by
  apply FastRouting.sound _ _ [258,96,24,36,129] 13 (by decide) (choices 1) [1,64,128] r16846 c16846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6116
  · exact u6117
  · exact u6118

def b16847 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 44 176 225 193 193 449), lower := (rows 259 98 28 44 176 32 64 128 256), losses := [] }

theorem u16847 : Upper (D 8) (R 8) [258,96,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16848 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 44 208 161 225 161 417), lower := (rows 259 98 28 44 208 32 64 128 256), losses := [] }

theorem u16848 : Upper (D 8) (R 8) [258,96,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16849 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 73 145 164 228 164 420), lower := (rows 259 98 28 73 145 32 64 128 256), losses := [] }

theorem u16849 : Upper (D 8) (R 8) [258,96,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16850 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 73 148 161 225 161 417), lower := (rows 259 98 28 73 148 32 64 128 256), losses := [] }

theorem u16850 : Upper (D 8) (R 8) [258,96,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16851 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 28 73 176 165 229 165 421), lower := (rows 259 98 28 73 176 32 64 128 256), losses := [] }

theorem u16851 : Upper (D 8) (R 8) [258,96,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16852 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 76 145 161 225 161 417), lower := (rows 259 98 28 76 145 32 64 128 256), losses := [] }

theorem u16852 : Upper (D 8) (R 8) [258,96,24,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16853 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 259 98 28 76 176 161 225 161 417), lower := (rows 259 98 28 76 176 32 64 128 256), losses := [] }

theorem u16853 : Upper (D 8) (R 8) [258,96,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16854 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 28 104 145 165 229 165 421), lower := (rows 259 98 28 104 145 32 64 128 256), losses := [] }

theorem u16854 : Upper (D 8) (R 8) [258,96,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16855 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 28 104 148 161 225 161 417), lower := (rows 259 98 28 104 148 32 64 128 256), losses := [] }

theorem u16855 : Upper (D 8) (R 8) [258,96,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16856 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 28 104 176 165 197 133 389), lower := (rows 259 98 28 104 176 32 64 128 256), losses := [] }

theorem u16856 : Upper (D 8) (R 8) [258,96,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16857 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 28 137 145 100 100 228 356), lower := (rows 259 98 28 137 145 32 64 128 256), losses := [] }

theorem u16857 : Upper (D 8) (R 8) [258,96,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16858 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 28 137 148 97 97 225 353), lower := (rows 259 98 28 137 148 32 64 128 256), losses := [] }

theorem u16858 : Upper (D 8) (R 8) [258,96,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16859 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 28 137 176 101 101 229 357), lower := (rows 259 98 28 137 176 32 64 128 256), losses := [] }

theorem u16859 : Upper (D 8) (R 8) [258,96,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16859
end Delivery.IrregularNine14.P08
