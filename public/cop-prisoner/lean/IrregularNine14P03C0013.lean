import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0001
import IrregularNine14P03C0002

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b780 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 265 208 33 240 176 432), lower := (rows 35 7 76 265 208 33 64 128 256), losses := [] }

theorem u780 : Upper (D 3) (R 3) [34,5,72,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b780
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 76 265 208 48 225 161 417), lower := (rows 35 7 76 265 208 48 64 128 256), losses := [] }

theorem u781 : Upper (D 3) (R 3) [34,5,72,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b781
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r782 : Route 9 := (fun mask => (mask,id))

def c782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u782 : Upper (D 3) (R 3) [34,5,72,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,5,72,257,192,128] 13 (by decide) (choices 1) [1,16,32] r782 c782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u113
  · exact u114
  · exact u115

def b783 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 145 33 224 224 480), lower := (rows 35 7 76 280 145 33 64 128 256), losses := [] }

theorem u783 : Upper (D 3) (R 3) [34,5,72,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b783
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 280 145 96 225 161 417), lower := (rows 35 7 76 280 145 96 64 128 256), losses := [] }

theorem u784 : Upper (D 3) (R 3) [34,5,72,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b784
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 97, camps := [], pairs := [(1,7)], upper := (rows 35 7 76 280 145 160 97 225 353), lower := (rows 35 7 76 280 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 18 20 24 16 32 65 0 257), good := (rows 355 327 76 286 351 32 64 0 256) }] }

theorem u785 : Upper (D 3) (R 3) [34,5,72,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b785
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 176 33 193 193 449), lower := (rows 35 7 76 280 176 33 64 128 256), losses := [] }

theorem u786 : Upper (D 3) (R 3) [34,5,72,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b786
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 280 176 96 193 129 385), lower := (rows 35 7 76 280 176 96 64 128 256), losses := [] }

theorem u787 : Upper (D 3) (R 3) [34,5,72,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b787
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 280 176 160 65 193 321), lower := (rows 35 7 76 280 176 160 64 128 256), losses := [] }

theorem u788 : Upper (D 3) (R 3) [34,5,72,272,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b788
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 392 112 33 209 145 401), lower := (rows 35 7 76 392 112 33 64 128 256), losses := [] }

theorem u789 : Upper (D 3) (R 3) [34,5,72,384,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b789
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 76 392 112 48 193 129 385), lower := (rows 35 7 76 392 112 48 64 128 256), losses := [] }

theorem u790 : Upper (D 3) (R 3) [34,5,72,384,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b790
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 392 112 160 81 145 273), lower := (rows 35 7 76 392 112 160 64 128 256), losses := [] }

theorem u791 : Upper (D 3) (R 3) [34,5,72,384,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b791
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 392 145 33 112 240 368), lower := (rows 35 7 76 392 145 33 64 128 256), losses := [] }

theorem u792 : Upper (D 3) (R 3) [34,5,72,384,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b792
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 7 76 392 145 48 97 225 353), lower := (rows 35 7 76 392 145 48 64 128 256), losses := [] }

theorem u793 : Upper (D 3) (R 3) [34,5,72,384,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b793
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 392 145 96 113 177 305), lower := (rows 35 7 76 392 145 96 64 128 256), losses := [] }

theorem u794 : Upper (D 3) (R 3) [34,5,72,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b794
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 392 176 33 81 209 337), lower := (rows 35 7 76 392 176 33 64 128 256), losses := [] }

theorem u795 : Upper (D 3) (R 3) [34,5,72,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b795
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 7 76 392 176 48 65 193 321), lower := (rows 35 7 76 392 176 48 64 128 256), losses := [] }

theorem u796 : Upper (D 3) (R 3) [34,5,72,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b796
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 392 176 96 81 145 273), lower := (rows 35 7 76 392 176 96 64 128 256), losses := [] }

theorem u797 : Upper (D 3) (R 3) [34,5,72,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b797
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 392 208 33 113 177 305), lower := (rows 35 7 76 392 208 33 64 128 256), losses := [] }

theorem u798 : Upper (D 3) (R 3) [34,5,72,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b798
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 76 392 208 48 97 161 289), lower := (rows 35 7 76 392 208 48 64 128 256), losses := [] }

theorem u799 : Upper (D 3) (R 3) [34,5,72,384,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b799
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 25 280 33 224 224 480), lower := (rows 35 7 196 25 280 33 64 128 256), losses := [] }

theorem u800 : Upper (D 3) (R 3) [34,5,192,17,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b800
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 25 280 96 225 161 417), lower := (rows 35 7 196 25 280 96 64 128 256), losses := [] }

theorem u801 : Upper (D 3) (R 3) [34,5,192,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b801
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 25 336 33 232 168 424), lower := (rows 35 7 196 25 336 33 64 128 256), losses := [] }

theorem u802 : Upper (D 3) (R 3) [34,5,192,17,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b802
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 196 25 336 40 225 161 417), lower := (rows 35 7 196 25 336 40 64 128 256), losses := [] }

theorem u803 : Upper (D 3) (R 3) [34,5,192,17,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b803
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 25 336 160 105 169 297), lower := (rows 35 7 196 25 336 160 64 128 256), losses := [] }

theorem u804 : Upper (D 3) (R 3) [34,5,192,17,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b804
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 56 273 33 200 200 456), lower := (rows 35 7 196 56 273 33 64 128 256), losses := [] }

theorem u805 : Upper (D 3) (R 3) [34,5,192,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b805
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 196 56 273 40 193 193 449), lower := (rows 35 7 196 56 273 40 64 128 256), losses := [] }

theorem u806 : Upper (D 3) (R 3) [34,5,192,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b806
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 56 273 96 201 137 393), lower := (rows 35 7 196 56 273 96 64 128 256), losses := [] }

theorem u807 : Upper (D 3) (R 3) [34,5,192,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b807
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 56 336 33 201 137 393), lower := (rows 35 7 196 56 336 33 64 128 256), losses := [] }

theorem u808 : Upper (D 3) (R 3) [34,5,192,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b808
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 196 56 336 40 193 129 385), lower := (rows 35 7 196 56 336 40 64 128 256), losses := [] }

theorem u809 : Upper (D 3) (R 3) [34,5,192,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b809
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 56 336 160 73 137 265), lower := (rows 35 7 196 56 336 160 64 128 256), losses := [] }

theorem u810 : Upper (D 3) (R 3) [34,5,192,48,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b810
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 176 33 329 393 265), lower := (rows 35 7 196 88 176 33 64 128 256), losses := [] }

theorem u811 : Upper (D 3) (R 3) [34,5,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b811
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 7 196 88 176 40 321 385 257), lower := (rows 35 7 196 88 176 40 64 128 256), losses := [] }

theorem u812 : Upper (D 3) (R 3) [34,5,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b812
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 7 196 88 176 288 73 137 265), lower := (rows 35 7 196 88 176 288 64 128 256), losses := [] }

theorem u813 : Upper (D 3) (R 3) [34,5,192,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b813
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 273 33 232 168 424), lower := (rows 35 7 196 88 273 33 64 128 256), losses := [] }

theorem u814 : Upper (D 3) (R 3) [34,5,192,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b814
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 196 88 273 40 225 161 417), lower := (rows 35 7 196 88 273 40 64 128 256), losses := [] }

theorem u815 : Upper (D 3) (R 3) [34,5,192,80,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b815
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 88 273 160 105 169 297), lower := (rows 35 7 196 88 273 160 64 128 256), losses := [] }

theorem u816 : Upper (D 3) (R 3) [34,5,192,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b816
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 304 33 201 137 393), lower := (rows 35 7 196 88 304 33 64 128 256), losses := [] }

theorem u817 : Upper (D 3) (R 3) [34,5,192,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b817
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 196 88 304 40 193 129 385), lower := (rows 35 7 196 88 304 40 64 128 256), losses := [] }

theorem u818 : Upper (D 3) (R 3) [34,5,192,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b818
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 88 304 160 73 137 265), lower := (rows 35 7 196 88 304 160 64 128 256), losses := [] }

theorem u819 : Upper (D 3) (R 3) [34,5,192,80,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b819
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 400 33 105 169 297), lower := (rows 35 7 196 88 400 33 64 128 256), losses := [] }

theorem u820 : Upper (D 3) (R 3) [34,5,192,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b820
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 196 88 400 40 97 161 289), lower := (rows 35 7 196 88 400 40 64 128 256), losses := [] }

theorem u821 : Upper (D 3) (R 3) [34,5,192,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b821
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 196 104 273 33 216 152 408), lower := (rows 35 7 196 104 273 33 64 128 256), losses := [] }

theorem u822 : Upper (D 3) (R 3) [34,5,192,96,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b822
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 7 196 104 273 40 209 145 401), lower := (rows 35 7 196 104 273 40 64 128 256), losses := [] }

theorem u823 : Upper (D 3) (R 3) [34,5,192,96,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b823
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 7 196 104 273 48 201 137 393), lower := (rows 35 7 196 104 273 48 64 128 256), losses := [] }

theorem u824 : Upper (D 3) (R 3) [34,5,192,96,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b824
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 104 273 160 89 153 281), lower := (rows 35 7 196 104 273 160 64 128 256), losses := [] }

theorem u825 : Upper (D 3) (R 3) [34,5,192,96,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b825
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 196 104 280 33 209 145 401), lower := (rows 35 7 196 104 280 33 64 128 256), losses := [] }

theorem u826 : Upper (D 3) (R 3) [34,5,192,96,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b826
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b827 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 196 104 280 48 193 129 385), lower := (rows 35 7 196 104 280 48 64 128 256), losses := [] }

theorem u827 : Upper (D 3) (R 3) [34,5,192,96,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b827
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b828 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 104 280 160 81 145 273), lower := (rows 35 7 196 104 280 160 64 128 256), losses := [] }

theorem u828 : Upper (D 3) (R 3) [34,5,192,96,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b828
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 196 104 400 33 89 153 281), lower := (rows 35 7 196 104 400 33 64 128 256), losses := [] }

theorem u829 : Upper (D 3) (R 3) [34,5,192,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b829
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 7 196 104 400 40 81 145 273), lower := (rows 35 7 196 104 400 40 64 128 256), losses := [] }

theorem u830 : Upper (D 3) (R 3) [34,5,192,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b830
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 7 196 104 400 48 73 137 265), lower := (rows 35 7 196 104 400 48 64 128 256), losses := [] }

theorem u831 : Upper (D 3) (R 3) [34,5,192,96,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b831
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 25 208 33 224 224 480), lower := (rows 35 7 268 25 208 33 64 128 256), losses := [] }

theorem u832 : Upper (D 3) (R 3) [34,5,264,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b832
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 161, camps := [], pairs := [(1,6)], upper := (rows 35 7 268 25 208 96 225 161 417), lower := (rows 35 7 268 25 208 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 32 0 129 257), good := (rows 419 391 270 415 144 32 0 128 256) }] }

theorem u833 : Upper (D 3) (R 3) [34,5,264,17,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b833
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 73 112 33 208 144 400), lower := (rows 35 7 268 73 112 33 64 128 256), losses := [] }

theorem u834 : Upper (D 3) (R 3) [34,5,264,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b834
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 268 73 112 48 193 129 385), lower := (rows 35 7 268 73 112 48 64 128 256), losses := [] }

theorem u835 : Upper (D 3) (R 3) [34,5,264,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b835
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r836 : Route 9 := (fun mask => (mask,id))

def c836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u836 : Upper (D 3) (R 3) [34,5,264,65,96,128] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,96,128] 13 (by decide) (choices 1) [1,16,128] r836 c836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u116
  · exact u117
  · exact u118

def b837 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 35 7 268 73 145 48 224 224 480), lower := (rows 35 7 268 73 145 48 64 128 256), losses := [] }

theorem u837 : Upper (D 3) (R 3) [34,5,264,65,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b837
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 268 73 145 96 240 176 432), lower := (rows 35 7 268 73 145 96 64 128 256), losses := [] }

theorem u838 : Upper (D 3) (R 3) [34,5,264,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b838
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r839 : Route 9 := (fun mask => (mask,id))

def c839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u839 : Upper (D 3) (R 3) [34,5,264,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,129,128] 13 (by decide) (choices 1) [16,32] r839 c839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u119
  · exact u120

#print axioms u839
end Delivery.IrregularNine14.P03
