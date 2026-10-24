import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0002

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 69 168 144 96 89 153 281), lower := (rows 275 38 69 168 144 96 64 128 256), losses := [] }

theorem u780 : Upper (D 0) (R 0) [274,36,65,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b780
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 69 200 144 33 120 184 312), lower := (rows 275 38 69 200 144 33 64 128 256), losses := [] }

theorem u781 : Upper (D 0) (R 0) [274,36,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b781
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 275 38 69 200 144 40 113 177 305), lower := (rows 275 38 69 200 144 40 64 128 256), losses := [] }

theorem u782 : Upper (D 0) (R 0) [274,36,65,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b782
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0)], upper := (rows 275 38 69 200 144 48 105 169 297), lower := (rows 275 38 69 200 144 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 152 185 64 128 256), good := (rows 306 38 102 248 176 48 64 176 256) }] }

theorem u783 : Upper (D 0) (R 0) [274,36,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b783
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 196 56 17 33 200 200 456), lower := (rows 275 38 196 56 17 33 64 128 256), losses := [] }

theorem u784 : Upper (D 0) (R 0) [274,36,192,48,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b784
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 38 196 56 17 40 193 193 449), lower := (rows 275 38 196 56 17 40 64 128 256), losses := [] }

theorem u785 : Upper (D 0) (R 0) [274,36,192,48,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b785
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 196 56 17 96 201 137 393), lower := (rows 275 38 196 56 17 96 64 128 256), losses := [] }

theorem u786 : Upper (D 0) (R 0) [274,36,192,48,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b786
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 275 38 196 73 17 40 240 176 432), lower := (rows 275 38 196 73 17 40 64 128 256), losses := [] }

theorem u787 : Upper (D 0) (R 0) [274,36,192,65,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b787
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 168, camps := [], pairs := [(1,0)], upper := (rows 275 38 196 73 17 48 232 168 424), lower := (rows 275 38 196 73 17 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 49 72 136 264), good := (rows 306 38 196 494 48 48 64 128 256) }] }

theorem u788 : Upper (D 0) (R 0) [274,36,192,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b788
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 196 73 17 160 120 184 312), lower := (rows 275 38 196 73 17 160 64 128 256), losses := [] }

theorem u789 : Upper (D 0) (R 0) [274,36,192,65,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b789
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 168, camps := [], pairs := [(1,4)], upper := (rows 275 38 196 88 17 33 232 168 424), lower := (rows 275 38 196 88 17 33 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 72 136 264), good := (rows 291 38 196 494 33 33 64 128 256) }] }

theorem u790 : Upper (D 0) (R 0) [274,36,192,80,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b790
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 275 38 196 88 17 40 225 161 417), lower := (rows 275 38 196 88 17 40 64 128 256), losses := [] }

theorem u791 : Upper (D 0) (R 0) [274,36,192,80,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b791
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 196 88 17 160 105 169 297), lower := (rows 275 38 196 88 17 160 64 128 256), losses := [] }

theorem u792 : Upper (D 0) (R 0) [274,36,192,80,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b792
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 152, camps := [], pairs := [(2,5)], upper := (rows 275 38 196 104 17 33 216 152 408), lower := (rows 275 38 196 104 17 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 49 0 72 136 264), good := (rows 275 22 196 476 17 17 64 128 256) }] }

theorem u793 : Upper (D 0) (R 0) [274,36,192,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b793
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 38 196 104 17 40 209 145 401), lower := (rows 275 38 196 104 17 40 64 128 256), losses := [] }

theorem u794 : Upper (D 0) (R 0) [274,36,192,96,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b794
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r795 : Route 9 := (fun mask => (mask,id))

def c795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u795 : Upper (D 0) (R 0) [274,36,192,96,1,16] 13 := by
  apply FastRouting.sound _ _ [274,36,192,96,1,16] 13 (by decide) (choices 1) [1,8,128] r795 c795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u127
  · exact u128
  · exact u129

def b796 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 196 104 17 160 89 153 281), lower := (rows 275 38 196 104 17 160 64 128 256), losses := [] }

theorem u796 : Upper (D 0) (R 0) [274,36,192,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b796
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 275 98 13 168 17 36 208 208 464), lower := (rows 275 98 13 168 17 36 64 128 256), losses := [] }

theorem u797 : Upper (D 0) (R 0) [274,96,9,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b797
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 196, camps := [], pairs := [(1,0)], upper := (rows 275 98 13 168 17 48 196 196 452), lower := (rows 275 98 13 168 17 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 49 68 132 260), good := (rows 306 98 494 168 48 48 64 128 256) }] }

theorem u798 : Upper (D 0) (R 0) [274,96,9,160,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b798
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 13 168 17 96 212 148 404), lower := (rows 275 98 13 168 17 96 64 128 256), losses := [] }

theorem u799 : Upper (D 0) (R 0) [274,96,9,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b799
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 13 168 17 160 84 212 340), lower := (rows 275 98 13 168 17 160 64 128 256), losses := [] }

theorem u800 : Upper (D 0) (R 0) [274,96,9,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b800
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r801 : Route 9 := (fun mask => (mask,id))

def c801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u801 : Upper (D 0) (R 0) [274,96,9,160,128,1] 13 := by
  apply FastRouting.sound _ _ [274,96,9,160,128,1] 13 (by decide) (choices 1) [4,16] r801 c801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u130
  · exact u131

def b802 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 275 98 13 168 144 36 81 209 337), lower := (rows 275 98 13 168 144 36 64 128 256), losses := [] }

theorem u802 : Upper (D 0) (R 0) [274,96,9,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b802
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 275 98 13 168 144 48 69 197 325), lower := (rows 275 98 13 168 144 48 64 128 256), losses := [] }

theorem u803 : Upper (D 0) (R 0) [274,96,9,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b803
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 13 168 144 96 85 149 277), lower := (rows 275 98 13 168 144 96 64 128 256), losses := [] }

theorem u804 : Upper (D 0) (R 0) [274,96,9,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b804
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 196, camps := [], pairs := [(1,0)], upper := (rows 275 98 28 168 17 33 196 196 452), lower := (rows 275 98 28 168 17 33 64 128 256), losses := [{ target := 0, region := (rows 0 42 5 42 16 32 117 181 309), good := (rows 478 490 478 490 468 494 64 128 256) }] }

theorem u805 : Upper (D 0) (R 0) [274,96,24,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b805
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 98 28 168 17 36 193 193 449), lower := (rows 275 98 28 168 17 36 64 128 256), losses := [] }

theorem u806 : Upper (D 0) (R 0) [274,96,24,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b806
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 28 168 17 96 197 133 389), lower := (rows 275 98 28 168 17 96 64 128 256), losses := [] }

theorem u807 : Upper (D 0) (R 0) [274,96,24,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b807
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 28 168 17 160 69 197 325), lower := (rows 275 98 28 168 17 160 64 128 256), losses := [] }

theorem u808 : Upper (D 0) (R 0) [274,96,24,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b808
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 44 88 17 33 196 132 388), lower := (rows 275 98 44 88 17 33 64 128 256), losses := [] }

theorem u809 : Upper (D 0) (R 0) [274,96,40,80,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b809
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 98 44 88 17 36 193 129 385), lower := (rows 275 98 44 88 17 36 64 128 256), losses := [] }

theorem u810 : Upper (D 0) (R 0) [274,96,40,80,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b810
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r811 : Route 9 := (fun mask => (mask,id))

def c811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u811 : Upper (D 0) (R 0) [274,96,40,80,1,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80,1,128] 13 (by decide) (choices 1) [1,4,128] r811 c811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u132
  · exact u133
  · exact u134

def r812 : Route 9 := (fun mask => (mask,id))

def c812 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u812 : Upper (D 0) (R 0) [274,96,40,80,128,1] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80,128,1] 13 (by decide) (choices 1) [1,4,128] r812 c812
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u135
  · exact u136
  · exact u137

def b813 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 98 44 88 144 36 193 129 385), lower := (rows 275 98 44 88 144 36 64 128 256), losses := [] }

theorem u813 : Upper (D 0) (R 0) [274,96,40,80,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b813
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 5, camps := [], pairs := [(1,0)], upper := (rows 275 98 44 88 144 160 69 133 261), lower := (rows 275 98 44 88 144 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 15 10 176 176 64 128 256), good := (rows 318 126 62 126 176 176 64 176 256) }] }

theorem u814 : Upper (D 0) (R 0) [274,96,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b814
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 275 98 44 137 17 36 208 208 464), lower := (rows 275 98 44 137 17 36 64 128 256), losses := [] }

theorem u815 : Upper (D 0) (R 0) [274,96,40,129,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b815
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 44 137 17 48 196 196 452), lower := (rows 275 98 44 137 17 48 64 128 256), losses := [] }

theorem u816 : Upper (D 0) (R 0) [274,96,40,129,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b816
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 44 137 17 96 212 148 404), lower := (rows 275 98 44 137 17 96 64 128 256), losses := [] }

theorem u817 : Upper (D 0) (R 0) [274,96,40,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b817
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 44 137 17 160 84 212 340), lower := (rows 275 98 44 137 17 160 64 128 256), losses := [] }

theorem u818 : Upper (D 0) (R 0) [274,96,40,129,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b818
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 44 137 144 33 84 212 340), lower := (rows 275 98 44 137 144 33 64 128 256), losses := [] }

theorem u819 : Upper (D 0) (R 0) [274,96,40,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b819
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 275 98 44 137 144 36 81 209 337), lower := (rows 275 98 44 137 144 36 64 128 256), losses := [] }

theorem u820 : Upper (D 0) (R 0) [274,96,40,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b820
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 52, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 44 137 144 48 69 197 325), lower := (rows 275 98 44 137 144 48 64 128 256), losses := [] }

theorem u821 : Upper (D 0) (R 0) [274,96,40,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b821
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 44 137 144 96 85 149 277), lower := (rows 275 98 44 137 144 96 64 128 256), losses := [] }

theorem u822 : Upper (D 0) (R 0) [274,96,40,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b822
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 44 152 17 33 196 196 452), lower := (rows 275 98 44 152 17 33 64 128 256), losses := [] }

theorem u823 : Upper (D 0) (R 0) [274,96,40,144,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b823
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 98 44 152 17 36 193 193 449), lower := (rows 275 98 44 152 17 36 64 128 256), losses := [] }

theorem u824 : Upper (D 0) (R 0) [274,96,40,144,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b824
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 44 152 17 96 197 133 389), lower := (rows 275 98 44 152 17 96 64 128 256), losses := [] }

theorem u825 : Upper (D 0) (R 0) [274,96,40,144,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b825
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 44 152 17 160 69 197 325), lower := (rows 275 98 44 152 17 160 64 128 256), losses := [] }

theorem u826 : Upper (D 0) (R 0) [274,96,40,144,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b826
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 148, camps := [], pairs := [(1,0)], upper := (rows 275 98 44 200 17 33 212 148 404), lower := (rows 275 98 44 200 17 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 38 57 16 32 65 129 257), good := (rows 478 110 46 200 472 494 64 128 256) }] }

theorem u827 : Upper (D 0) (R 0) [274,96,40,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b827
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 98 44 200 17 36 209 145 401), lower := (rows 275 98 44 200 17 36 64 128 256), losses := [] }

theorem u828 : Upper (D 0) (R 0) [274,96,40,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b828
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r829 : Route 9 := (fun mask => (mask,id))

def c829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u829 : Upper (D 0) (R 0) [274,96,40,192,1,16] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192,1,16] 13 (by decide) (choices 1) [1,4,128] r829 c829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u138
  · exact u139
  · exact u140

def b830 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 44 200 17 160 85 149 277), lower := (rows 275 98 44 200 17 160 64 128 256), losses := [] }

theorem u830 : Upper (D 0) (R 0) [274,96,40,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b830
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r831 : Route 9 := (fun mask => (mask,id))

def c831 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u831 : Upper (D 0) (R 0) [274,96,40,192,128,1] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192,128,1] 13 (by decide) (choices 1) [1,4,16] r831 c831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u141
  · exact u142
  · exact u143

def b832 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 275 98 44 200 144 36 81 145 273), lower := (rows 275 98 44 200 144 36 64 128 256), losses := [] }

theorem u832 : Upper (D 0) (R 0) [274,96,40,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b832
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 44 200 144 48 69 133 261), lower := (rows 275 98 44 200 144 48 64 128 256), losses := [] }

theorem u833 : Upper (D 0) (R 0) [274,96,40,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b833
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 275 98 52 137 17 36 200 200 456), lower := (rows 275 98 52 137 17 36 64 128 256), losses := [] }

theorem u834 : Upper (D 0) (R 0) [274,96,48,129,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b834
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 275 98 52 137 17 40 196 196 452), lower := (rows 275 98 52 137 17 40 64 128 256), losses := [] }

theorem u835 : Upper (D 0) (R 0) [274,96,48,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b835
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 140, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 275 98 52 137 17 96 204 140 396), lower := (rows 275 98 52 137 17 96 64 128 256), losses := [] }

theorem u836 : Upper (D 0) (R 0) [274,96,48,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b836
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 76, camps := [{ cop := 3, region := 52, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 137 17 160 76 204 332), lower := (rows 275 98 52 137 17 160 64 128 256), losses := [] }

theorem u837 : Upper (D 0) (R 0) [274,96,48,129,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b837
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 137 144 33 76 204 332), lower := (rows 275 98 52 137 144 33 64 128 256), losses := [] }

theorem u838 : Upper (D 0) (R 0) [274,96,48,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b838
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 275 98 52 137 144 36 73 201 329), lower := (rows 275 98 52 137 144 36 64 128 256), losses := [] }

theorem u839 : Upper (D 0) (R 0) [274,96,48,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b839
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P00
