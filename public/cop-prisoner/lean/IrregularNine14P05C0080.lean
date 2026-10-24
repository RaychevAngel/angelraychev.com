import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0028

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4800 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 148 44 26 288 73 137 265), lower := (rows 35 70 148 44 26 288 64 128 256), losses := [] }

theorem u4800 : Upper (D 5) (R 5) [34,68,144,36,10,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4801 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 44 273 33 74 138 266), lower := (rows 35 70 148 44 273 33 64 128 256), losses := [] }

theorem u4801 : Upper (D 5) (R 5) [34,68,144,36,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4802 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 148 44 273 34 73 137 265), lower := (rows 35 70 148 44 273 34 64 128 256), losses := [] }

theorem u4802 : Upper (D 5) (R 5) [34,68,144,36,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4802
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4803 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 148 44 273 40 75 139 267), lower := (rows 35 70 148 44 273 40 64 128 256), losses := [] }

theorem u4803 : Upper (D 5) (R 5) [34,68,144,36,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4804 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 44 274 33 73 137 265), lower := (rows 35 70 148 44 274 33 64 128 256), losses := [] }

theorem u4804 : Upper (D 5) (R 5) [34,68,144,36,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4805 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 148 44 274 40 73 137 265), lower := (rows 35 70 148 44 274 40 64 128 256), losses := [] }

theorem u4805 : Upper (D 5) (R 5) [34,68,144,36,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4805
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4806 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 44 280 33 75 139 267), lower := (rows 35 70 148 44 280 33 64 128 256), losses := [] }

theorem u4806 : Upper (D 5) (R 5) [34,68,144,36,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4807 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 148 44 280 34 73 137 265), lower := (rows 35 70 148 44 280 34 64 128 256), losses := [] }

theorem u4807 : Upper (D 5) (R 5) [34,68,144,36,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4808 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 148 44 280 40 67 131 259), lower := (rows 35 70 148 44 280 40 64 128 256), losses := [] }

theorem u4808 : Upper (D 5) (R 5) [34,68,144,36,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4808
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4809 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 265 26 33 108 172 300), lower := (rows 35 70 148 265 26 33 64 128 256), losses := [] }

theorem u4809 : Upper (D 5) (R 5) [34,68,144,257,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4810 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 148 265 26 36 105 169 297), lower := (rows 35 70 148 265 26 36 64 128 256), losses := [] }

theorem u4810 : Upper (D 5) (R 5) [34,68,144,257,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4810
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4811 : Route 9 := (fun mask => (mask,id))

def c4811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4811 : Upper (D 5) (R 5) [34,68,144,257,10,8] 13 := by
  apply FastRouting.sound _ _ [34,68,144,257,10,8] 13 (by decide) (choices 1) [1,4,32] r4811 c4811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1714
  · exact u1715
  · exact u1716

def b4812 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 198, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 148 265 56 33 78 142 270), lower := (rows 35 70 148 265 56 33 64 128 256), losses := [] }

theorem u4812 : Upper (D 5) (R 5) [34,68,144,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4813 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 148 265 56 34 77 141 269), lower := (rows 35 70 148 265 56 34 64 128 256), losses := [] }

theorem u4813 : Upper (D 5) (R 5) [34,68,144,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4814 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 148 265 56 36 75 139 267), lower := (rows 35 70 148 265 56 36 64 128 256), losses := [] }

theorem u4814 : Upper (D 5) (R 5) [34,68,144,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4815 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 148 265 56 40 71 135 263), lower := (rows 35 70 148 265 56 40 64 128 256), losses := [] }

theorem u4815 : Upper (D 5) (R 5) [34,68,144,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4816 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 266 25 33 108 172 300), lower := (rows 35 70 148 266 25 33 64 128 256), losses := [] }

theorem u4816 : Upper (D 5) (R 5) [34,68,144,258,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4817 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 148 266 25 36 105 169 297), lower := (rows 35 70 148 266 25 36 64 128 256), losses := [] }

theorem u4817 : Upper (D 5) (R 5) [34,68,144,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4818 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 148 266 25 40 101 165 293), lower := (rows 35 70 148 266 25 40 64 128 256), losses := [] }

theorem u4818 : Upper (D 5) (R 5) [34,68,144,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4819 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 266 56 33 77 141 269), lower := (rows 35 70 148 266 56 33 64 128 256), losses := [] }

theorem u4819 : Upper (D 5) (R 5) [34,68,144,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4820 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 148 266 56 36 73 137 265), lower := (rows 35 70 148 266 56 36 64 128 256), losses := [] }

theorem u4820 : Upper (D 5) (R 5) [34,68,144,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4821 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 148 266 56 40 69 133 261), lower := (rows 35 70 148 266 56 40 64 128 256), losses := [] }

theorem u4821 : Upper (D 5) (R 5) [34,68,144,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4822 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 268 25 33 106 170 298), lower := (rows 35 70 148 268 25 33 64 128 256), losses := [] }

theorem u4822 : Upper (D 5) (R 5) [34,68,144,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4823 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 148 268 25 34 105 169 297), lower := (rows 35 70 148 268 25 34 64 128 256), losses := [] }

theorem u4823 : Upper (D 5) (R 5) [34,68,144,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4824 : PairBound 9 := { available := 35, camps := [], pairs := [(1,3),(2,3)], upper := (rows 35 70 148 268 25 40 99 163 291), lower := (rows 35 70 148 268 25 40 64 128 256), losses := [{ target := 3, region := (rows 1 18 20 0 16 32 65 129 257), good := (rows 483 70 150 260 471 32 64 128 256) }] }

theorem u4824 : Upper (D 5) (R 5) [34,68,144,260,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4825 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 268 26 33 105 169 297), lower := (rows 35 70 148 268 26 33 64 128 256), losses := [] }

theorem u4825 : Upper (D 5) (R 5) [34,68,144,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4826 : Route 9 := (fun mask => (mask,id))

def c4826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4826 : Upper (D 5) (R 5) [34,68,144,260,10,8] 13 := by
  apply FastRouting.sound _ _ [34,68,144,260,10,8] 13 (by decide) (choices 1) [1,32] r4826 c4826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1717
  · exact u1718

def b4827 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 268 56 33 75 139 267), lower := (rows 35 70 148 268 56 33 64 128 256), losses := [] }

theorem u4827 : Upper (D 5) (R 5) [34,68,144,260,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4827
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4828 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 148 268 56 34 73 137 265), lower := (rows 35 70 148 268 56 34 64 128 256), losses := [] }

theorem u4828 : Upper (D 5) (R 5) [34,68,144,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4829 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 148 268 56 40 67 131 259), lower := (rows 35 70 148 268 56 40 64 128 256), losses := [] }

theorem u4829 : Upper (D 5) (R 5) [34,68,144,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4830 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 148 296 26 33 77 141 269), lower := (rows 35 70 148 296 26 33 64 128 256), losses := [] }

theorem u4830 : Upper (D 5) (R 5) [34,68,144,288,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4831 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 35 70 148 296 26 36 73 137 265), lower := (rows 35 70 148 296 26 36 64 128 256), losses := [] }

theorem u4831 : Upper (D 5) (R 5) [34,68,144,288,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4832 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 148 296 26 40 69 133 261), lower := (rows 35 70 148 296 26 40 64 128 256), losses := [] }

theorem u4832 : Upper (D 5) (R 5) [34,68,144,288,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4833 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 265 26 33 92 156 284), lower := (rows 35 70 164 265 26 33 64 128 256), losses := [] }

theorem u4833 : Upper (D 5) (R 5) [34,68,160,257,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4834 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 164 265 26 36 89 153 281), lower := (rows 35 70 164 265 26 36 64 128 256), losses := [] }

theorem u4834 : Upper (D 5) (R 5) [34,68,160,257,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4835 : Route 9 := (fun mask => (mask,id))

def c4835 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4835 : Upper (D 5) (R 5) [34,68,160,257,10,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,10,8] 13 (by decide) (choices 1) [1,4,16] r4835 c4835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1719
  · exact u1720
  · exact u1721

def b4836 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 164 265 26 48 77 141 269), lower := (rows 35 70 164 265 26 48 64 128 256), losses := [] }

theorem u4836 : Upper (D 5) (R 5) [34,68,160,257,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4837 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 265 28 33 90 154 282), lower := (rows 35 70 164 265 28 33 64 128 256), losses := [] }

theorem u4837 : Upper (D 5) (R 5) [34,68,160,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4837
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4838 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 265 28 34 89 153 281), lower := (rows 35 70 164 265 28 34 64 128 256), losses := [] }

theorem u4838 : Upper (D 5) (R 5) [34,68,160,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4839 : Route 9 := (fun mask => (mask,id))

def c4839 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4839 : Upper (D 5) (R 5) [34,68,160,257,12,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257,12,8] 13 (by decide) (choices 1) [1,2,16] r4839 c4839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1722
  · exact u1723
  · exact u1724

def b4840 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(3,2)], upper := (rows 35 70 164 265 28 48 75 139 267), lower := (rows 35 70 164 265 28 48 64 128 256), losses := [] }

theorem u4840 : Upper (D 5) (R 5) [34,68,160,257,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4841 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 266 25 33 92 156 284), lower := (rows 35 70 164 266 25 33 64 128 256), losses := [] }

theorem u4841 : Upper (D 5) (R 5) [34,68,160,258,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4841
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4842 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 164 266 25 36 89 153 281), lower := (rows 35 70 164 266 25 36 64 128 256), losses := [] }

theorem u4842 : Upper (D 5) (R 5) [34,68,160,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4842
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4843 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 70 164 266 25 40 85 149 277), lower := (rows 35 70 164 266 25 40 64 128 256), losses := [] }

theorem u4843 : Upper (D 5) (R 5) [34,68,160,258,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4844 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 164 266 25 48 77 141 269), lower := (rows 35 70 164 266 25 48 64 128 256), losses := [] }

theorem u4844 : Upper (D 5) (R 5) [34,68,160,258,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4845 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 266 28 33 89 153 281), lower := (rows 35 70 164 266 28 33 64 128 256), losses := [] }

theorem u4845 : Upper (D 5) (R 5) [34,68,160,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4846 : Route 9 := (fun mask => (mask,id))

def c4846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4846 : Upper (D 5) (R 5) [34,68,160,258,12,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,258,12,8] 13 (by decide) (choices 1) [1,16] r4846 c4846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1725
  · exact u1726

def b4847 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 4 }], pairs := [(3,2)], upper := (rows 35 70 164 266 28 48 73 137 265), lower := (rows 35 70 164 266 28 48 64 128 256), losses := [] }

theorem u4847 : Upper (D 5) (R 5) [34,68,160,258,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4847
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4848 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 268 25 33 90 154 282), lower := (rows 35 70 164 268 25 33 64 128 256), losses := [] }

theorem u4848 : Upper (D 5) (R 5) [34,68,160,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4848
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4849 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 268 25 34 89 153 281), lower := (rows 35 70 164 268 25 34 64 128 256), losses := [] }

theorem u4849 : Upper (D 5) (R 5) [34,68,160,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4850 : Route 9 := (fun mask => (mask,id))

def c4850 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4850 : Upper (D 5) (R 5) [34,68,160,260,9,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,260,9,8] 13 (by decide) (choices 1) [1,2,16] r4850 c4850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1727
  · exact u1728
  · exact u1729

def r4851 : Route 9 := (fun mask => (mask,id))

def c4851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4851 : Upper (D 5) (R 5) [34,68,160,260,9,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,260,9,16] 13 (by decide) (choices 1) [1,2,8] r4851 c4851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1730
  · exact u1731
  · exact u1732

def b4852 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 268 26 33 89 153 281), lower := (rows 35 70 164 268 26 33 64 128 256), losses := [] }

theorem u4852 : Upper (D 5) (R 5) [34,68,160,260,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4852
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4853 : Route 9 := (fun mask => (mask,id))

def c4853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4853 : Upper (D 5) (R 5) [34,68,160,260,10,8] 13 := by
  apply FastRouting.sound _ _ [34,68,160,260,10,8] 13 (by decide) (choices 1) [1,16] r4853 c4853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1733
  · exact u1734

def b4854 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 164 268 26 48 73 137 265), lower := (rows 35 70 164 268 26 48 64 128 256), losses := [] }

theorem u4854 : Upper (D 5) (R 5) [34,68,160,260,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4855 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 280 25 33 78 142 270), lower := (rows 35 70 164 280 25 33 64 128 256), losses := [] }

theorem u4855 : Upper (D 5) (R 5) [34,68,160,272,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4855
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4856 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 164 280 25 34 77 141 269), lower := (rows 35 70 164 280 25 34 64 128 256), losses := [] }

theorem u4856 : Upper (D 5) (R 5) [34,68,160,272,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4857 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 280, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 164 280 25 36 75 139 267), lower := (rows 35 70 164 280 25 36 64 128 256), losses := [] }

theorem u4857 : Upper (D 5) (R 5) [34,68,160,272,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4858 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 164 280 25 40 71 135 263), lower := (rows 35 70 164 280 25 40 64 128 256), losses := [] }

theorem u4858 : Upper (D 5) (R 5) [34,68,160,272,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4859 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 164 280 26 33 77 141 269), lower := (rows 35 70 164 280 26 33 64 128 256), losses := [] }

theorem u4859 : Upper (D 5) (R 5) [34,68,160,272,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4859
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4859
end Delivery.IrregularNine14.P05
