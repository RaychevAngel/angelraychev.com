import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0001

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 134 265 48 96 210 146 402), lower := (rows 53 74 134 265 48 96 64 128 256), losses := [] }

theorem u780 : Upper (D 1) (R 1) [52,72,130,257,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b780
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 134 265 80 160 114 178 306), lower := (rows 53 74 134 265 80 160 64 128 256), losses := [] }

theorem u781 : Upper (D 1) (R 1) [52,72,130,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b781
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 134 280 80 33 226 162 418), lower := (rows 53 74 134 280 80 33 64 128 256), losses := [] }

theorem u782 : Upper (D 1) (R 1) [52,72,130,272,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b782
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 134 280 80 34 225 161 417), lower := (rows 53 74 134 280 80 34 64 128 256), losses := [] }

theorem u783 : Upper (D 1) (R 1) [52,72,130,272,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b783
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 134 280 80 160 99 163 291), lower := (rows 53 74 134 280 80 160 64 128 256), losses := [] }

theorem u784 : Upper (D 1) (R 1) [52,72,130,272,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b784
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 196 280 18 33 226 162 418), lower := (rows 53 74 196 280 18 33 64 128 256), losses := [] }

theorem u785 : Upper (D 1) (R 1) [52,72,192,272,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b785
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 196 280 18 34 225 161 417), lower := (rows 53 74 196 280 18 34 64 128 256), losses := [] }

theorem u786 : Upper (D 1) (R 1) [52,72,192,272,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b786
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 196 280 18 160 99 163 291), lower := (rows 53 74 196 280 18 160 64 128 256), losses := [] }

theorem u787 : Upper (D 1) (R 1) [52,72,192,272,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b787
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 74 196 392 17 34 114 178 306), lower := (rows 53 74 196 392 17 34 64 128 256), losses := [] }

theorem u788 : Upper (D 1) (R 1) [52,72,192,384,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b788
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 196 392 18 34 113 177 305), lower := (rows 53 74 196 392 18 34 64 128 256), losses := [] }

theorem u789 : Upper (D 1) (R 1) [52,72,192,384,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b789
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 196 392 18 48 99 163 291), lower := (rows 53 74 196 392 18 48 64 128 256), losses := [] }

theorem u790 : Upper (D 1) (R 1) [52,72,192,384,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b790
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 261 138 18 96 240 176 432), lower := (rows 53 74 261 138 18 96 64 128 256), losses := [] }

theorem u791 : Upper (D 1) (R 1) [52,72,257,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b791
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 261 138 18 160 112 240 368), lower := (rows 53 74 261 138 18 160 64 128 256), losses := [] }

theorem u792 : Upper (D 1) (R 1) [52,72,257,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b792
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 261 138 48 96 210 146 402), lower := (rows 53 74 261 138 48 96 64 128 256), losses := [] }

theorem u793 : Upper (D 1) (R 1) [52,72,257,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b793
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 261 138 48 160 82 210 338), lower := (rows 53 74 261 138 48 160 64 128 256), losses := [] }

theorem u794 : Upper (D 1) (R 1) [52,72,257,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b794
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r795 : Route 9 := (fun mask => (mask,id))

def c795 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u795 : Upper (D 1) (R 1) [52,72,257,130,64,128] 13 := by
  apply FastRouting.sound _ _ [52,72,257,130,64,128] 13 (by decide) (choices 1) [2,16,32] r795 c795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u71
  · exact u72
  · exact u73

def b796 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 137 18 96 240 176 432), lower := (rows 53 74 262 137 18 96 64 128 256), losses := [] }

theorem u796 : Upper (D 1) (R 1) [52,72,258,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b796
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 137 18 160 112 240 368), lower := (rows 53 74 262 137 18 160 64 128 256), losses := [] }

theorem u797 : Upper (D 1) (R 1) [52,72,258,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b797
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 262 137 48 96 210 146 402), lower := (rows 53 74 262 137 48 96 64 128 256), losses := [] }

theorem u798 : Upper (D 1) (R 1) [52,72,258,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b798
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 262 137 48 160 82 210 338), lower := (rows 53 74 262 137 48 160 64 128 256), losses := [] }

theorem u799 : Upper (D 1) (R 1) [52,72,258,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b799
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r800 : Route 9 := (fun mask => (mask,id))

def c800 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u800 : Upper (D 1) (R 1) [52,72,258,129,64,128] 13 := by
  apply FastRouting.sound _ _ [52,72,258,129,64,128] 13 (by decide) (choices 1) [2,16,32] r800 c800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u74
  · exact u75
  · exact u76

def b801 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 262 152 80 33 226 162 418), lower := (rows 53 74 262 152 80 33 64 128 256), losses := [] }

theorem u801 : Upper (D 1) (R 1) [52,72,258,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b801
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 53 74 262 152 80 34 225 161 417), lower := (rows 53 74 262 152 80 34 64 128 256), losses := [] }

theorem u802 : Upper (D 1) (R 1) [52,72,258,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b802
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r803 : Route 9 := (fun mask => (mask,id))

def c803 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u803 : Upper (D 1) (R 1) [52,72,258,144,64,128] 13 := by
  apply FastRouting.sound _ _ [52,72,258,144,64,128] 13 (by decide) (choices 1) [1,2,32] r803 c803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u77
  · exact u78
  · exact u79

def b804 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 324 11 18 160 240 176 432), lower := (rows 53 74 324 11 18 160 64 128 256), losses := [] }

theorem u804 : Upper (D 1) (R 1) [52,72,320,3,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b804
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 11 48 160 210 146 402), lower := (rows 53 74 324 11 48 160 64 128 256), losses := [] }

theorem u805 : Upper (D 1) (R 1) [52,72,320,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b805
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 324 11 144 160 114 178 306), lower := (rows 53 74 324 11 144 160 64 128 256), losses := [] }

theorem u806 : Upper (D 1) (R 1) [52,72,320,3,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b806
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 324 26 144 33 226 162 418), lower := (rows 53 74 324 26 144 33 64 128 256), losses := [] }

theorem u807 : Upper (D 1) (R 1) [52,72,320,18,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b807
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 469, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 324 26 144 34 225 161 417), lower := (rows 53 74 324 26 144 34 64 128 256), losses := [] }

theorem u808 : Upper (D 1) (R 1) [52,72,320,18,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b808
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 324 26 144 160 99 163 291), lower := (rows 53 74 324 26 144 160 64 128 256), losses := [] }

theorem u809 : Upper (D 1) (R 1) [52,72,320,18,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b809
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 50, camps := [], pairs := [(3,6)], upper := (rows 53 74 324 137 18 160 114 178 306), lower := (rows 53 74 324 137 18 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 187 0 146 274), good := (rows 445 442 260 169 434 160 0 160 256) }] }

theorem u810 : Upper (D 1) (R 1) [52,72,320,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b810
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 137 48 160 82 146 274), lower := (rows 53 74 324 137 48 160 64 128 256), losses := [] }

theorem u811 : Upper (D 1) (R 1) [52,72,320,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b811
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 74 324 138 17 160 114 178 306), lower := (rows 53 74 324 138 17 160 64 128 256), losses := [] }

theorem u812 : Upper (D 1) (R 1) [52,72,320,130,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b812
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 324 138 18 160 113 177 305), lower := (rows 53 74 324 138 18 160 64 128 256), losses := [] }

theorem u813 : Upper (D 1) (R 1) [52,72,320,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b813
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 324 138 48 160 83 147 275), lower := (rows 53 74 324 138 48 160 64 128 256), losses := [] }

theorem u814 : Upper (D 1) (R 1) [52,72,320,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b814
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 74 324 152 18 33 226 162 418), lower := (rows 53 74 324 152 18 33 64 128 256), losses := [] }

theorem u815 : Upper (D 1) (R 1) [52,72,320,144,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b815
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 324 152 18 34 225 161 417), lower := (rows 53 74 324 152 18 34 64 128 256), losses := [] }

theorem u816 : Upper (D 1) (R 1) [52,72,320,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b816
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r817 : Route 9 := (fun mask => (mask,id))

def c817 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u817 : Upper (D 1) (R 1) [52,72,320,144,2,128] 13 := by
  apply FastRouting.sound _ _ [52,72,320,144,2,128] 13 (by decide) (choices 1) [1,2,32] r817 c817
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u80
  · exact u81
  · exact u82

def b818 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 388 11 18 96 240 176 432), lower := (rows 53 74 388 11 18 96 64 128 256), losses := [] }

theorem u818 : Upper (D 1) (R 1) [52,72,384,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b818
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 11 48 96 210 146 402), lower := (rows 53 74 388 11 48 96 64 128 256), losses := [] }

theorem u819 : Upper (D 1) (R 1) [52,72,384,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b819
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 74 388 11 80 160 114 178 306), lower := (rows 53 74 388 11 80 160 64 128 256), losses := [] }

theorem u820 : Upper (D 1) (R 1) [52,72,384,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b820
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 74 388 138 17 96 114 178 306), lower := (rows 53 74 388 138 17 96 64 128 256), losses := [] }

theorem u821 : Upper (D 1) (R 1) [52,72,384,130,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b821
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 74 388 138 18 96 113 177 305), lower := (rows 53 74 388 138 18 96 64 128 256), losses := [] }

theorem u822 : Upper (D 1) (R 1) [52,72,384,130,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b822
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 74 388 138 48 96 83 147 275), lower := (rows 53 74 388 138 48 96 64 128 256), losses := [] }

theorem u823 : Upper (D 1) (R 1) [52,72,384,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b823
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 53 74 388 152 18 33 98 226 354), lower := (rows 53 74 388 152 18 33 64 128 256), losses := [] }

theorem u824 : Upper (D 1) (R 1) [52,72,384,144,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b824
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 388 152 18 34 97 225 353), lower := (rows 53 74 388 152 18 34 64 128 256), losses := [] }

theorem u825 : Upper (D 1) (R 1) [52,72,384,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b825
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r826 : Route 9 := (fun mask => (mask,id))

def c826 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u826 : Upper (D 1) (R 1) [52,72,384,144,2,64] 13 := by
  apply FastRouting.sound _ _ [52,72,384,144,2,64] 13 (by decide) (choices 1) [1,2,32] r826 c826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u83
  · exact u84
  · exact u85

def b827 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 53 74 388 152 80 33 98 162 290), lower := (rows 53 74 388 152 80 33 64 128 256), losses := [] }

theorem u827 : Upper (D 1) (R 1) [52,72,384,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b827
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r828 : Route 9 := (fun mask => (mask,id))

def c828 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u828 : Upper (D 1) (R 1) [52,72,384,144,64,2] 13 := by
  apply FastRouting.sound _ _ [52,72,384,144,64,2] 13 (by decide) (choices 1) [1,2,32] r828 c828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u86
  · exact u87
  · exact u88

def b829 : PairBound 9 := { available := 162, camps := [], pairs := [(2,4)], upper := (rows 53 82 76 265 144 34 226 162 418), lower := (rows 53 82 76 265 144 34 64 128 256), losses := [{ target := 4, region := (rows 1 2 5 9 0 34 98 162 290), good := (rows 493 482 76 269 128 482 64 128 256) }] }

theorem u829 : Upper (D 1) (R 1) [52,80,72,257,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b829
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 76 265 144 160 98 162 290), lower := (rows 53 82 76 265 144 160 64 128 256), losses := [] }

theorem u830 : Upper (D 1) (R 1) [52,80,72,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b830
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 76 266 144 33 226 162 418), lower := (rows 53 82 76 266 144 33 64 128 256), losses := [] }

theorem u831 : Upper (D 1) (R 1) [52,80,72,258,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b831
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6)], upper := (rows 53 82 76 266 144 34 225 161 417), lower := (rows 53 82 76 266 144 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 149 42 0 133 261), good := (rows 437 50 445 298 144 34 0 144 256) }] }

theorem u832 : Upper (D 1) (R 1) [52,80,72,258,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b832
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 76 266 144 160 99 163 291), lower := (rows 53 82 76 266 144 160 64 128 256), losses := [] }

theorem u833 : Upper (D 1) (R 1) [52,80,72,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b833
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 53 82 262 42 144 33 200 200 456), lower := (rows 53 82 262 42 144 33 64 128 256), losses := [] }

theorem u834 : Upper (D 1) (R 1) [52,80,258,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b834
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 53 82 262 42 144 40 193 193 449), lower := (rows 53 82 262 42 144 40 64 128 256), losses := [] }

theorem u835 : Upper (D 1) (R 1) [52,80,258,34,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b835
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b836 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 262 42 144 96 201 137 393), lower := (rows 53 82 262 42 144 96 64 128 256), losses := [] }

theorem u836 : Upper (D 1) (R 1) [52,80,258,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b836
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b837 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 262 42 144 160 73 201 329), lower := (rows 53 82 262 42 144 160 64 128 256), losses := [] }

theorem u837 : Upper (D 1) (R 1) [52,80,258,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b837
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 262 73 144 34 232 168 424), lower := (rows 53 82 262 73 144 34 64 128 256), losses := [] }

theorem u838 : Upper (D 1) (R 1) [52,80,258,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b838
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 262 73 144 40 226 162 418), lower := (rows 53 82 262 73 144 40 64 128 256), losses := [] }

theorem u839 : Upper (D 1) (R 1) [52,80,258,65,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b839
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P01
