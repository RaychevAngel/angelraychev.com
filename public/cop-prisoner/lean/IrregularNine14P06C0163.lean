import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0018

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9780 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 104 274 33 84 212 340), lower := (rows 7 35 140 104 274 33 64 128 256), losses := [] }

theorem u9780 : Upper (D 6) (R 6) [6,33,136,96,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9780
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9781 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 104 274 36 81 209 337), lower := (rows 7 35 140 104 274 36 64 128 256), losses := [] }

theorem u9781 : Upper (D 6) (R 6) [6,33,136,96,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9781
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9782 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 140 104 274 48 69 197 325), lower := (rows 7 35 140 104 274 48 64 128 256), losses := [] }

theorem u9782 : Upper (D 6) (R 6) [6,33,136,96,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9782
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9783 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 104 274 96 85 149 277), lower := (rows 7 35 140 104 274 96 64 128 256), losses := [] }

theorem u9783 : Upper (D 6) (R 6) [6,33,136,96,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9783
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9784 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 104 276 33 82 210 338), lower := (rows 7 35 140 104 276 33 64 128 256), losses := [] }

theorem u9784 : Upper (D 6) (R 6) [6,33,136,96,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9784
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9785 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 104 276 34 81 209 337), lower := (rows 7 35 140 104 276 34 64 128 256), losses := [] }

theorem u9785 : Upper (D 6) (R 6) [6,33,136,96,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9785
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9786 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 104 276 48 67 195 323), lower := (rows 7 35 140 104 276 48 64 128 256), losses := [] }

theorem u9786 : Upper (D 6) (R 6) [6,33,136,96,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9786
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9787 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 104 276 96 83 147 275), lower := (rows 7 35 140 104 276 96 64 128 256), losses := [] }

theorem u9787 : Upper (D 6) (R 6) [6,33,136,96,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9787
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9788 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 104 336 33 86 150 278), lower := (rows 7 35 140 104 336 33 64 128 256), losses := [] }

theorem u9788 : Upper (D 6) (R 6) [6,33,136,96,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9788
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9789 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 104 336 34 85 149 277), lower := (rows 7 35 140 104 336 34 64 128 256), losses := [] }

theorem u9789 : Upper (D 6) (R 6) [6,33,136,96,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9789
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9790 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 104 336 36 83 147 275), lower := (rows 7 35 140 104 336 36 64 128 256), losses := [] }

theorem u9790 : Upper (D 6) (R 6) [6,33,136,96,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9790
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9791 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 104 336 48 71 135 263), lower := (rows 7 35 140 104 336 48 64 128 256), losses := [] }

theorem u9791 : Upper (D 6) (R 6) [6,33,136,96,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9791
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9792 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 265 82 36 112 240 368), lower := (rows 7 35 140 265 82 36 64 128 256), losses := [] }

theorem u9792 : Upper (D 6) (R 6) [6,33,136,257,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9792
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9793 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 140 265 82 48 100 228 356), lower := (rows 7 35 140 265 82 48 64 128 256), losses := [] }

theorem u9793 : Upper (D 6) (R 6) [6,33,136,257,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9793
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9794 : Route 9 := (fun mask => (mask,id))

def c9794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9794 : Upper (D 6) (R 6) [6,33,136,257,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,257,66,64] 13 (by decide) (choices 1) [4,16,32] r9794 c9794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1115
  · exact u1116
  · exact u1117

def b9795 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 265 84 34 112 240 368), lower := (rows 7 35 140 265 84 34 64 128 256), losses := [] }

theorem u9795 : Upper (D 6) (R 6) [6,33,136,257,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9795
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9796 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 265 84 48 98 226 354), lower := (rows 7 35 140 265 84 48 64 128 256), losses := [] }

theorem u9796 : Upper (D 6) (R 6) [6,33,136,257,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9796
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9797 : Route 9 := (fun mask => (mask,id))

def c9797 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9797 : Upper (D 6) (R 6) [6,33,136,257,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,257,68,64] 13 (by decide) (choices 1) [2,16,32] r9797 c9797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1118
  · exact u1119
  · exact u1120

def b9798 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 265 112 34 84 212 340), lower := (rows 7 35 140 265 112 34 64 128 256), losses := [] }

theorem u9798 : Upper (D 6) (R 6) [6,33,136,257,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9798
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9799 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 265 112 36 82 210 338), lower := (rows 7 35 140 265 112 36 64 128 256), losses := [] }

theorem u9799 : Upper (D 6) (R 6) [6,33,136,257,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9799
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9800 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 265 112 48 70 198 326), lower := (rows 7 35 140 265 112 48 64 128 256), losses := [] }

theorem u9800 : Upper (D 6) (R 6) [6,33,136,257,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9800
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9801 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 265 112 96 86 150 278), lower := (rows 7 35 140 265 112 96 64 128 256), losses := [] }

theorem u9801 : Upper (D 6) (R 6) [6,33,136,257,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9801
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9802 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 266 81 36 112 240 368), lower := (rows 7 35 140 266 81 36 64 128 256), losses := [] }

theorem u9802 : Upper (D 6) (R 6) [6,33,136,258,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9802
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9803 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 140 266 81 48 100 228 356), lower := (rows 7 35 140 266 81 48 64 128 256), losses := [] }

theorem u9803 : Upper (D 6) (R 6) [6,33,136,258,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9803
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9804 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 140 266 81 96 116 180 308), lower := (rows 7 35 140 266 81 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 127 73 137 265), good := (rows 501 497 492 508 497 96 96 128 256) }] }

theorem u9804 : Upper (D 6) (R 6) [6,33,136,258,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9804
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9805 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 266 84 33 112 240 368), lower := (rows 7 35 140 266 84 33 64 128 256), losses := [] }

theorem u9805 : Upper (D 6) (R 6) [6,33,136,258,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9805
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9806 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 266 84 48 97 225 353), lower := (rows 7 35 140 266 84 48 64 128 256), losses := [] }

theorem u9806 : Upper (D 6) (R 6) [6,33,136,258,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9806
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9807 : Route 9 := (fun mask => (mask,id))

def c9807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9807 : Upper (D 6) (R 6) [6,33,136,258,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,258,68,64] 13 (by decide) (choices 1) [1,16,32] r9807 c9807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1121
  · exact u1122
  · exact u1123

def b9808 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 266 112 33 84 212 340), lower := (rows 7 35 140 266 112 33 64 128 256), losses := [] }

theorem u9808 : Upper (D 6) (R 6) [6,33,136,258,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9808
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9809 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 266 112 36 81 209 337), lower := (rows 7 35 140 266 112 36 64 128 256), losses := [] }

theorem u9809 : Upper (D 6) (R 6) [6,33,136,258,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9809
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9810 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 266 112 48 69 197 325), lower := (rows 7 35 140 266 112 48 64 128 256), losses := [] }

theorem u9810 : Upper (D 6) (R 6) [6,33,136,258,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9810
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9811 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 266 112 96 85 149 277), lower := (rows 7 35 140 266 112 96 64 128 256), losses := [] }

theorem u9811 : Upper (D 6) (R 6) [6,33,136,258,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9811
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9812 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 268 81 34 112 240 368), lower := (rows 7 35 140 268 81 34 64 128 256), losses := [] }

theorem u9812 : Upper (D 6) (R 6) [6,33,136,260,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9812
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9813 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 114, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 268 81 48 98 226 354), lower := (rows 7 35 140 268 81 48 64 128 256), losses := [] }

theorem u9813 : Upper (D 6) (R 6) [6,33,136,260,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9813
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9814 : Route 9 := (fun mask => (mask,id))

def c9814 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9814 : Upper (D 6) (R 6) [6,33,136,260,65,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,260,65,64] 13 (by decide) (choices 1) [2,16,32] r9814 c9814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1124
  · exact u1125
  · exact u1126

def b9815 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 268 82 33 112 240 368), lower := (rows 7 35 140 268 82 33 64 128 256), losses := [] }

theorem u9815 : Upper (D 6) (R 6) [6,33,136,260,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9815
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9816 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 114, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 140 268 82 48 97 225 353), lower := (rows 7 35 140 268 82 48 64 128 256), losses := [] }

theorem u9816 : Upper (D 6) (R 6) [6,33,136,260,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9816
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9817 : Route 9 := (fun mask => (mask,id))

def c9817 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9817 : Upper (D 6) (R 6) [6,33,136,260,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,260,66,64] 13 (by decide) (choices 1) [1,16,32] r9817 c9817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1127
  · exact u1128
  · exact u1129

def b9818 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 268 112 33 82 210 338), lower := (rows 7 35 140 268 112 33 64 128 256), losses := [] }

theorem u9818 : Upper (D 6) (R 6) [6,33,136,260,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9818
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9819 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 268 112 34 81 209 337), lower := (rows 7 35 140 268 112 34 64 128 256), losses := [] }

theorem u9819 : Upper (D 6) (R 6) [6,33,136,260,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9819
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9820 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 268 112 48 67 195 323), lower := (rows 7 35 140 268 112 48 64 128 256), losses := [] }

theorem u9820 : Upper (D 6) (R 6) [6,33,136,260,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9820
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9821 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 268 112 96 83 147 275), lower := (rows 7 35 140 268 112 96 64 128 256), losses := [] }

theorem u9821 : Upper (D 6) (R 6) [6,33,136,260,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9821
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9822 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 280 81 34 100 228 356), lower := (rows 7 35 140 280 81 34 64 128 256), losses := [] }

theorem u9822 : Upper (D 6) (R 6) [6,33,136,272,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9822
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9823 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 280 81 36 98 226 354), lower := (rows 7 35 140 280 81 36 64 128 256), losses := [] }

theorem u9823 : Upper (D 6) (R 6) [6,33,136,272,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9823
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9824 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 7 35 140 280 81 96 102 166 294), lower := (rows 7 35 140 280 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 115 65 129 257), good := (rows 486 482 140 316 508 96 96 128 256) }] }

theorem u9824 : Upper (D 6) (R 6) [6,33,136,272,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9824
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9825 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 280 82 33 100 228 356), lower := (rows 7 35 140 280 82 33 64 128 256), losses := [] }

theorem u9825 : Upper (D 6) (R 6) [6,33,136,272,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9825
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9826 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 280 82 36 97 225 353), lower := (rows 7 35 140 280 82 36 64 128 256), losses := [] }

theorem u9826 : Upper (D 6) (R 6) [6,33,136,272,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9826
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9827 : Route 9 := (fun mask => (mask,id))

def c9827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9827 : Upper (D 6) (R 6) [6,33,136,272,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272,66,64] 13 (by decide) (choices 1) [1,4,32] r9827 c9827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1130
  · exact u1131
  · exact u1132

def b9828 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 280 84 33 98 226 354), lower := (rows 7 35 140 280 84 33 64 128 256), losses := [] }

theorem u9828 : Upper (D 6) (R 6) [6,33,136,272,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9828
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9829 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 280 84 34 97 225 353), lower := (rows 7 35 140 280 84 34 64 128 256), losses := [] }

theorem u9829 : Upper (D 6) (R 6) [6,33,136,272,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9829
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9830 : Route 9 := (fun mask => (mask,id))

def c9830 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9830 : Upper (D 6) (R 6) [6,33,136,272,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,272,68,64] 13 (by decide) (choices 1) [1,2,32] r9830 c9830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1133
  · exact u1134
  · exact u1135

def b9831 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 280 112 33 70 198 326), lower := (rows 7 35 140 280 112 33 64 128 256), losses := [] }

theorem u9831 : Upper (D 6) (R 6) [6,33,136,272,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9831
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9832 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 280 112 34 69 197 325), lower := (rows 7 35 140 280 112 34 64 128 256), losses := [] }

theorem u9832 : Upper (D 6) (R 6) [6,33,136,272,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9832
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9833 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 280 112 36 67 195 323), lower := (rows 7 35 140 280 112 36 64 128 256), losses := [] }

theorem u9833 : Upper (D 6) (R 6) [6,33,136,272,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9833
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9834 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 140 280 112 96 71 135 263), lower := (rows 7 35 140 280 112 96 64 128 256), losses := [] }

theorem u9834 : Upper (D 6) (R 6) [6,33,136,272,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9834
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9835 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 296 81 34 84 212 340), lower := (rows 7 35 140 296 81 34 64 128 256), losses := [] }

theorem u9835 : Upper (D 6) (R 6) [6,33,136,288,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9835
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9836 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 296 81 36 82 210 338), lower := (rows 7 35 140 296 81 36 64 128 256), losses := [] }

theorem u9836 : Upper (D 6) (R 6) [6,33,136,288,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9836
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9837 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 140 296 81 48 70 198 326), lower := (rows 7 35 140 296 81 48 64 128 256), losses := [] }

theorem u9837 : Upper (D 6) (R 6) [6,33,136,288,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9837
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9838 : Route 9 := (fun mask => (mask,id))

def c9838 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9838 : Upper (D 6) (R 6) [6,33,136,288,65,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,65,64] 13 (by decide) (choices 1) [2,4,16] r9838 c9838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1136
  · exact u1137
  · exact u1138

def b9839 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 296 82 33 84 212 340), lower := (rows 7 35 140 296 82 33 64 128 256), losses := [] }

theorem u9839 : Upper (D 6) (R 6) [6,33,136,288,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9839
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9839
end Delivery.IrregularNine14.P06
