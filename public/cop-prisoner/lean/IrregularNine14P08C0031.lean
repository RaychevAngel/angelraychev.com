import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 28 200 304 36 225 161 417), lower := (rows 35 67 28 200 304 36 64 128 256), losses := [] }

theorem u1860 : Upper (D 8) (R 8) [34,65,24,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1860 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1861 : Route 9 := (fun mask => (mask,id))

def c1861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1861 : Upper (D 8) (R 8) [34,65,24,192,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,24,192,288,128] 13 (by decide) (choices 1) [1,4,32] r1861 c1861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u255
  · exact u256
  · exact u257

def b1862 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 88 176 33 452 388 388), lower := (rows 35 67 44 88 176 33 64 128 256), losses := [] }

theorem u1862 : Upper (D 8) (R 8) [34,65,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 67 44 88 176 36 449 385 385), lower := (rows 35 67 44 88 176 36 64 128 256), losses := [] }

theorem u1863 : Upper (D 8) (R 8) [34,65,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1863 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 176 160 325 389 261), lower := (rows 35 67 44 88 176 160 64 128 256), losses := [] }

theorem u1864 : Upper (D 8) (R 8) [34,65,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 88 176 288 197 133 389), lower := (rows 35 67 44 88 176 288 64 128 256), losses := [] }

theorem u1865 : Upper (D 8) (R 8) [34,65,40,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1865 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 88 304 33 196 132 388), lower := (rows 35 67 44 88 304 33 64 128 256), losses := [] }

theorem u1866 : Upper (D 8) (R 8) [34,65,40,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 88 304 36 193 129 385), lower := (rows 35 67 44 88 304 36 64 128 256), losses := [] }

theorem u1867 : Upper (D 8) (R 8) [34,65,40,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1867 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1868 : Route 9 := (fun mask => (mask,id))

def c1868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1868 : Upper (D 8) (R 8) [34,65,40,80,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,288,128] 13 (by decide) (choices 1) [1,4,128] r1868 c1868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u258
  · exact u259
  · exact u260

def b1869 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 88 400 33 228 164 420), lower := (rows 35 67 44 88 400 33 64 128 256), losses := [] }

theorem u1869 : Upper (D 8) (R 8) [34,65,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1870 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 88 400 36 225 161 417), lower := (rows 35 67 44 88 400 36 64 128 256), losses := [] }

theorem u1870 : Upper (D 8) (R 8) [34,65,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1870 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 88 400 160 101 165 293), lower := (rows 35 67 44 88 400 160 64 128 256), losses := [] }

theorem u1871 : Upper (D 8) (R 8) [34,65,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 304 33 208 208 464), lower := (rows 35 67 44 140 304 33 64 128 256), losses := [] }

theorem u1872 : Upper (D 8) (R 8) [34,65,40,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1873 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 140 304 48 193 193 449), lower := (rows 35 67 44 140 304 48 64 128 256), losses := [] }

theorem u1873 : Upper (D 8) (R 8) [34,65,40,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1873 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1874 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 140 304 96 209 145 401), lower := (rows 35 67 44 140 304 96 64 128 256), losses := [] }

theorem u1874 : Upper (D 8) (R 8) [34,65,40,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 304 160 81 209 337), lower := (rows 35 67 44 140 304 160 64 128 256), losses := [] }

theorem u1875 : Upper (D 8) (R 8) [34,65,40,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1876 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 336 33 240 176 432), lower := (rows 35 67 44 140 336 33 64 128 256), losses := [] }

theorem u1876 : Upper (D 8) (R 8) [34,65,40,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1877 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 140 336 48 225 161 417), lower := (rows 35 67 44 140 336 48 64 128 256), losses := [] }

theorem u1877 : Upper (D 8) (R 8) [34,65,40,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1877 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 140 336 160 113 177 305), lower := (rows 35 67 44 140 336 160 64 128 256), losses := [] }

theorem u1878 : Upper (D 8) (R 8) [34,65,40,132,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 152 276 33 224 224 480), lower := (rows 35 67 44 152 276 33 64 128 256), losses := [] }

theorem u1879 : Upper (D 8) (R 8) [34,65,40,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 152 276 96 225 161 417), lower := (rows 35 67 44 152 276 96 64 128 256), losses := [] }

theorem u1880 : Upper (D 8) (R 8) [34,65,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 276 160 97 225 353), lower := (rows 35 67 44 152 276 160 64 128 256), losses := [] }

theorem u1881 : Upper (D 8) (R 8) [34,65,40,144,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1882 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 152 304 33 196 196 452), lower := (rows 35 67 44 152 304 33 64 128 256), losses := [] }

theorem u1882 : Upper (D 8) (R 8) [34,65,40,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 152 304 36 193 193 449), lower := (rows 35 67 44 152 304 36 64 128 256), losses := [] }

theorem u1883 : Upper (D 8) (R 8) [34,65,40,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1883 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 152 304 96 197 133 389), lower := (rows 35 67 44 152 304 96 64 128 256), losses := [] }

theorem u1884 : Upper (D 8) (R 8) [34,65,40,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 304 160 69 197 325), lower := (rows 35 67 44 152 304 160 64 128 256), losses := [] }

theorem u1885 : Upper (D 8) (R 8) [34,65,40,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 152 336 33 228 164 420), lower := (rows 35 67 44 152 336 33 64 128 256), losses := [] }

theorem u1886 : Upper (D 8) (R 8) [34,65,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 152 336 36 225 161 417), lower := (rows 35 67 44 152 336 36 64 128 256), losses := [] }

theorem u1887 : Upper (D 8) (R 8) [34,65,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1887 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 336 160 101 165 293), lower := (rows 35 67 44 152 336 160 64 128 256), losses := [] }

theorem u1888 : Upper (D 8) (R 8) [34,65,40,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 200 176 33 340 404 276), lower := (rows 35 67 44 200 176 33 64 128 256), losses := [] }

theorem u1889 : Upper (D 8) (R 8) [34,65,40,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1890 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 67 44 200 176 36 337 401 273), lower := (rows 35 67 44 200 176 36 64 128 256), losses := [] }

theorem u1890 : Upper (D 8) (R 8) [34,65,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1890 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1891 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 35 67 44 200 176 48 325 389 261), lower := (rows 35 67 44 200 176 48 64 128 256), losses := [] }

theorem u1891 : Upper (D 8) (R 8) [34,65,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1891 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 44 200 176 288 85 149 277), lower := (rows 35 67 44 200 176 288 64 128 256), losses := [] }

theorem u1892 : Upper (D 8) (R 8) [34,65,40,192,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1892 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 200 276 33 240 176 432), lower := (rows 35 67 44 200 276 33 64 128 256), losses := [] }

theorem u1893 : Upper (D 8) (R 8) [34,65,40,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 200 276 48 225 161 417), lower := (rows 35 67 44 200 276 48 64 128 256), losses := [] }

theorem u1894 : Upper (D 8) (R 8) [34,65,40,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1894 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 276 160 113 177 305), lower := (rows 35 67 44 200 276 160 64 128 256), losses := [] }

theorem u1895 : Upper (D 8) (R 8) [34,65,40,192,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 200 304 33 212 148 404), lower := (rows 35 67 44 200 304 33 64 128 256), losses := [] }

theorem u1896 : Upper (D 8) (R 8) [34,65,40,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 200 304 36 209 145 401), lower := (rows 35 67 44 200 304 36 64 128 256), losses := [] }

theorem u1897 : Upper (D 8) (R 8) [34,65,40,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1897 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1898 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 200 304 48 197 133 389), lower := (rows 35 67 44 200 304 48 64 128 256), losses := [] }

theorem u1898 : Upper (D 8) (R 8) [34,65,40,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1898 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1899 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 304 160 85 149 277), lower := (rows 35 67 44 200 304 160 64 128 256), losses := [] }

theorem u1899 : Upper (D 8) (R 8) [34,65,40,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 200 400 33 116 180 308), lower := (rows 35 67 44 200 400 33 64 128 256), losses := [] }

theorem u1900 : Upper (D 8) (R 8) [34,65,40,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 44 200 400 36 113 177 305), lower := (rows 35 67 44 200 400 36 64 128 256), losses := [] }

theorem u1901 : Upper (D 8) (R 8) [34,65,40,192,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1901 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 44 200 400 48 101 165 293), lower := (rows 35 67 44 200 400 48 64 128 256), losses := [] }

theorem u1902 : Upper (D 8) (R 8) [34,65,40,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1902 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 268 176 33 208 208 464), lower := (rows 35 67 44 268 176 33 64 128 256), losses := [] }

theorem u1903 : Upper (D 8) (R 8) [34,65,40,260,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 268 176 48 193 193 449), lower := (rows 35 67 44 268 176 48 64 128 256), losses := [] }

theorem u1904 : Upper (D 8) (R 8) [34,65,40,260,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1904 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1905 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 268 176 96 209 145 401), lower := (rows 35 67 44 268 176 96 64 128 256), losses := [] }

theorem u1905 : Upper (D 8) (R 8) [34,65,40,260,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1906 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 268 176 160 81 209 337), lower := (rows 35 67 44 268 176 160 64 128 256), losses := [] }

theorem u1906 : Upper (D 8) (R 8) [34,65,40,260,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 268 208 33 240 176 432), lower := (rows 35 67 44 268 208 33 64 128 256), losses := [] }

theorem u1907 : Upper (D 8) (R 8) [34,65,40,260,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 268 208 48 225 161 417), lower := (rows 35 67 44 268 208 48 64 128 256), losses := [] }

theorem u1908 : Upper (D 8) (R 8) [34,65,40,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1908 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1909 : Route 9 := (fun mask => (mask,id))

def c1909 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1909 : Upper (D 8) (R 8) [34,65,40,260,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,260,192,128] 13 (by decide) (choices 1) [1,16,32] r1909 c1909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u261
  · exact u262
  · exact u263

def b1910 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 280 148 33 224 224 480), lower := (rows 35 67 44 280 148 33 64 128 256), losses := [] }

theorem u1910 : Upper (D 8) (R 8) [34,65,40,272,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 280 148 96 225 161 417), lower := (rows 35 67 44 280 148 96 64 128 256), losses := [] }

theorem u1911 : Upper (D 8) (R 8) [34,65,40,272,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 280 148 160 97 225 353), lower := (rows 35 67 44 280 148 160 64 128 256), losses := [] }

theorem u1912 : Upper (D 8) (R 8) [34,65,40,272,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 280 176 33 196 196 452), lower := (rows 35 67 44 280 176 33 64 128 256), losses := [] }

theorem u1913 : Upper (D 8) (R 8) [34,65,40,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 280 176 36 193 193 449), lower := (rows 35 67 44 280 176 36 64 128 256), losses := [] }

theorem u1914 : Upper (D 8) (R 8) [34,65,40,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1914 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 280 176 96 197 133 389), lower := (rows 35 67 44 280 176 96 64 128 256), losses := [] }

theorem u1915 : Upper (D 8) (R 8) [34,65,40,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 280 176 160 69 197 325), lower := (rows 35 67 44 280 176 160 64 128 256), losses := [] }

theorem u1916 : Upper (D 8) (R 8) [34,65,40,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 44 280 208 33 228 164 420), lower := (rows 35 67 44 280 208 33 64 128 256), losses := [] }

theorem u1917 : Upper (D 8) (R 8) [34,65,40,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 44 280 208 36 225 161 417), lower := (rows 35 67 44 280 208 36 64 128 256), losses := [] }

theorem u1918 : Upper (D 8) (R 8) [34,65,40,272,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1918 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1919 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 280 208 160 101 165 293), lower := (rows 35 67 44 280 208 160 64 128 256), losses := [] }

theorem u1919 : Upper (D 8) (R 8) [34,65,40,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P08
