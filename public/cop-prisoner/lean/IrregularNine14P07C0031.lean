import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0001

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 196 73 176 288 80 131 259), lower := (rows 7 42 196 73 176 288 80 128 256), losses := [] }

theorem u1860 : Upper (D 7) (R 7) [6,40,192,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1860 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1861 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 72, targets := 160 }], pairs := [(3,5),(3,7),(4,1),(4,6)], upper := (rows 7 42 196 73 273 160 66 176 304), lower := (rows 7 42 196 73 273 160 66 128 256), losses := [] }

theorem u1861 : Upper (D 7) (R 7) [6,40,192,65,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1862 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 273 160 80 162 290), lower := (rows 7 42 196 73 273 160 80 128 256), losses := [] }

theorem u1862 : Upper (D 7) (R 7) [6,40,192,65,257,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1862 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 7 42 196 73 273 160 96 146 274), lower := (rows 7 42 196 73 273 160 96 128 256), losses := [] }

theorem u1863 : Upper (D 7) (R 7) [6,40,192,65,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 274 48 65 160 416), lower := (rows 7 42 196 73 274 48 65 128 256), losses := [] }

theorem u1864 : Upper (D 7) (R 7) [6,40,192,65,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1864 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 132, targets := 34 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 7 42 196 73 274 48 96 129 385), lower := (rows 7 42 196 73 274 48 96 128 256), losses := [] }

theorem u1865 : Upper (D 7) (R 7) [6,40,192,65,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1865 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 73 274 48 192 161 289), lower := (rows 7 42 196 73 274 48 192 128 256), losses := [] }

theorem u1866 : Upper (D 7) (R 7) [6,40,192,65,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1866 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 274 160 65 176 304), lower := (rows 7 42 196 73 274 160 65 128 256), losses := [] }

theorem u1867 : Upper (D 7) (R 7) [6,40,192,65,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 3, region := 164, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 7 42 196 73 274 160 80 161 289), lower := (rows 7 42 196 73 274 160 80 128 256), losses := [] }

theorem u1868 : Upper (D 7) (R 7) [6,40,192,65,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1868 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1869 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 7 42 196 73 274 160 96 145 273), lower := (rows 7 42 196 73 274 160 96 128 256), losses := [] }

theorem u1869 : Upper (D 7) (R 7) [6,40,192,65,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1870 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 304 160 65 146 274), lower := (rows 7 42 196 73 304 160 65 128 256), losses := [] }

theorem u1870 : Upper (D 7) (R 7) [6,40,192,65,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 72, targets := 160 }], pairs := [(3,5),(3,7),(4,1),(4,6)], upper := (rows 7 42 196 73 304 160 66 145 273), lower := (rows 7 42 196 73 304 160 66 128 256), losses := [] }

theorem u1871 : Upper (D 7) (R 7) [6,40,192,65,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(0,5),(1,6),(4,6)], upper := (rows 7 42 196 73 304 160 80 131 259), lower := (rows 7 42 196 73 304 160 80 128 256), losses := [{ target := 5, region := (rows 3 2 12 8 16 0 80 131 259), good := (rows 391 399 196 461 336 128 80 128 256) }] }

theorem u1872 : Upper (D 7) (R 7) [6,40,192,65,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1872 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1873 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 400 48 65 162 290), lower := (rows 7 42 196 73 400 48 65 128 256), losses := [] }

theorem u1873 : Upper (D 7) (R 7) [6,40,192,65,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1873 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1874 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 196 73 400 48 66 161 289), lower := (rows 7 42 196 73 400 48 66 128 256), losses := [] }

theorem u1874 : Upper (D 7) (R 7) [6,40,192,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1874 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 100, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 42 196 73 400 48 96 131 259), lower := (rows 7 42 196 73 400 48 96 128 256), losses := [] }

theorem u1875 : Upper (D 7) (R 7) [6,40,192,65,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1875 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1876 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 88 146 33 65 416 288), lower := (rows 7 42 196 88 146 33 65 128 256), losses := [] }

theorem u1876 : Upper (D 7) (R 7) [6,40,192,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1877 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 146 33 96 385 257), lower := (rows 7 42 196 88 146 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 32 98 128 256), good := (rows 70 106 196 92 222 96 96 128 256) }] }

theorem u1877 : Upper (D 7) (R 7) [6,40,192,80,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 176, targets := 64 }], pairs := [(2,1),(3,1),(4,6)], upper := (rows 7 42 196 88 146 33 320 161 289), lower := (rows 7 42 196 88 146 33 320 128 256), losses := [{ target := 1, region := (rows 1 0 55 24 16 33 355 161 289), good := (rows 485 492 196 92 220 485 320 128 320) }] }

theorem u1878 : Upper (D 7) (R 7) [6,40,192,80,130,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1878 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 88 146 288 65 161 289), lower := (rows 7 42 196 88 146 288 65 128 256), losses := [] }

theorem u1879 : Upper (D 7) (R 7) [6,40,192,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1879 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 146 288 96 129 257), lower := (rows 7 42 196 88 146 288 96 128 256), losses := [] }

theorem u1880 : Upper (D 7) (R 7) [6,40,192,80,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1880 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 88 176 33 65 386 258), lower := (rows 7 42 196 88 176 33 65 128 256), losses := [] }

theorem u1881 : Upper (D 7) (R 7) [6,40,192,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1882 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 78, targets := 1 },{ cop := 0, region := 432, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 196 88 176 33 66 385 257), lower := (rows 7 42 196 88 176 33 66 128 256), losses := [] }

theorem u1882 : Upper (D 7) (R 7) [6,40,192,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 196 88 176 33 320 131 259), lower := (rows 7 42 196 88 176 33 320 128 256), losses := [] }

theorem u1883 : Upper (D 7) (R 7) [6,40,192,80,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1883 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 196 88 273 160 65 162 290), lower := (rows 7 42 196 88 273 160 65 128 256), losses := [] }

theorem u1884 : Upper (D 7) (R 7) [6,40,192,80,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 66 }], pairs := [(2,1),(3,0),(4,1),(4,6)], upper := (rows 7 42 196 88 273 160 66 161 289), lower := (rows 7 42 196 88 273 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 164 67 128 256), good := (rows 102 106 228 88 344 160 66 160 256) },{ target := 1, region := (rows 1 0 12 8 17 189 64 145 273), good := (rows 437 44 228 508 433 160 64 160 256) }] }

theorem u1885 : Upper (D 7) (R 7) [6,40,192,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 3 },{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 273 160 96 131 259), lower := (rows 7 42 196 88 273 160 96 128 256), losses := [] }

theorem u1886 : Upper (D 7) (R 7) [6,40,192,80,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,6)], upper := (rows 7 42 196 88 274 33 65 160 416), lower := (rows 7 42 196 88 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 19 32 64 162 290), good := (rows 406 442 204 88 402 432 88 128 256) }] }

theorem u1887 : Upper (D 7) (R 7) [6,40,192,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,1),(3,0),(4,5),(4,6)], upper := (rows 7 42 196 88 274 33 96 129 385), lower := (rows 7 42 196 88 274 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 98 128 256), good := (rows 70 106 196 88 346 96 96 128 256) }] }

theorem u1888 : Upper (D 7) (R 7) [6,40,192,80,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 88 274 33 192 161 289), lower := (rows 7 42 196 88 274 33 192 128 256), losses := [] }

theorem u1889 : Upper (D 7) (R 7) [6,40,192,80,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1890 : Route 9 := (fun mask => (mask,id))

def c1890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1890 : Upper (D 7) (R 7) [6,40,192,80,258,128,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,258,128,1] 13 (by decide) (choices 1) [1,32] r1890 c1890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u86
  · exact u87

def b1891 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 68, targets := 3 },{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 274 160 96 129 257), lower := (rows 7 42 196 88 274 160 96 128 256), losses := [] }

theorem u1891 : Upper (D 7) (R 7) [6,40,192,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 88 304 33 65 130 386), lower := (rows 7 42 196 88 304 33 65 128 256), losses := [] }

theorem u1892 : Upper (D 7) (R 7) [6,40,192,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 88 304 33 66 129 385), lower := (rows 7 42 196 88 304 33 66 128 256), losses := [] }

theorem u1893 : Upper (D 7) (R 7) [6,40,192,80,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 88 304 33 192 131 259), lower := (rows 7 42 196 88 304 33 192 128 256), losses := [] }

theorem u1894 : Upper (D 7) (R 7) [6,40,192,80,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(4,6)], upper := (rows 7 42 196 88 304 160 65 131 259), lower := (rows 7 42 196 88 304 160 65 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 81 229 0 129 257), good := (rows 439 42 180 58 304 160 433 160 256) }] }

theorem u1895 : Upper (D 7) (R 7) [6,40,192,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 88 304 160 66 129 257), lower := (rows 7 42 196 88 304 160 66 128 256), losses := [] }

theorem u1896 : Upper (D 7) (R 7) [6,40,192,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 400, targets := 65 }], pairs := [(1,6),(3,0),(4,0),(4,6)], upper := (rows 7 42 196 88 400 33 65 162 290), lower := (rows 7 42 196 88 400 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 19 32 64 130 258), good := (rows 406 442 204 88 400 48 88 128 256) },{ target := 6, region := (rows 1 10 4 8 123 97 0 139 267), good := (rows 439 442 180 442 400 433 433 128 256) }] }

theorem u1897 : Upper (D 7) (R 7) [6,40,192,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1898 : Route 9 := (fun mask => (mask,id))

def c1898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1898 : Upper (D 7) (R 7) [6,40,192,80,384,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384,1,2] 13 (by decide) (choices 1) [1,32] r1898 c1898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u88
  · exact u89

def r1899 : Route 9 := (fun mask => (mask,id))

def c1899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1899 : Upper (D 7) (R 7) [6,40,192,80,384,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384,1,32] 13 (by decide) (choices 1) [1,2] r1899 c1899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u90
  · exact u91

def b1900 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 428, targets := 2 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 7 42 196 265 81 160 66 176 304), lower := (rows 7 42 196 265 81 160 66 128 256), losses := [] }

theorem u1900 : Upper (D 7) (R 7) [6,40,192,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 7 42 196 265 81 160 80 162 290), lower := (rows 7 42 196 265 81 160 80 128 256), losses := [] }

theorem u1901 : Upper (D 7) (R 7) [6,40,192,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1901 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 5, region := 68, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(3,6)], upper := (rows 7 42 196 265 81 160 96 146 274), lower := (rows 7 42 196 265 81 160 96 128 256), losses := [] }

theorem u1902 : Upper (D 7) (R 7) [6,40,192,257,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 114, targets := 128 },{ cop := 4, region := 164, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 7 42 196 265 82 48 65 160 416), lower := (rows 7 42 196 265 82 48 65 128 256), losses := [] }

theorem u1903 : Upper (D 7) (R 7) [6,40,192,257,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1903 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 42 196 265 82 48 96 129 385), lower := (rows 7 42 196 265 82 48 96 128 256), losses := [] }

theorem u1904 : Upper (D 7) (R 7) [6,40,192,257,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1904 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1905 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 265 82 48 192 161 289), lower := (rows 7 42 196 265 82 48 192 128 256), losses := [] }

theorem u1905 : Upper (D 7) (R 7) [6,40,192,257,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1905 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1906 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 160 },{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1),(4,5),(4,7)], upper := (rows 7 42 196 265 82 160 65 176 304), lower := (rows 7 42 196 265 82 160 65 128 256), losses := [] }

theorem u1906 : Upper (D 7) (R 7) [6,40,192,257,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 7 42 196 265 82 160 80 161 289), lower := (rows 7 42 196 265 82 160 80 128 256), losses := [] }

theorem u1907 : Upper (D 7) (R 7) [6,40,192,257,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1907 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 265 82 160 96 145 273), lower := (rows 7 42 196 265 82 160 96 128 256), losses := [] }

theorem u1908 : Upper (D 7) (R 7) [6,40,192,257,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 132, targets := 35 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(2,5)], upper := (rows 7 42 196 265 112 34 65 144 400), lower := (rows 7 42 196 265 112 34 65 128 256), losses := [] }

theorem u1909 : Upper (D 7) (R 7) [6,40,192,257,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 42 196 265 112 34 80 129 385), lower := (rows 7 42 196 265 112 34 80 128 256), losses := [] }

theorem u1910 : Upper (D 7) (R 7) [6,40,192,257,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1910 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 265 112 34 192 145 273), lower := (rows 7 42 196 265 112 34 192 128 256), losses := [] }

theorem u1911 : Upper (D 7) (R 7) [6,40,192,257,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(1,0),(2,0),(4,0),(4,1)], upper := (rows 7 42 196 265 112 160 65 146 274), lower := (rows 7 42 196 265 112 160 65 128 256), losses := [{ target := 0, region := (rows 0 10 68 8 84 237 64 129 257), good := (rows 438 42 244 426 116 160 500 160 256) }] }

theorem u1912 : Upper (D 7) (R 7) [6,40,192,257,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 80, targets := 129 },{ cop := 2, region := 48, targets := 2 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 7 42 196 265 112 160 66 145 273), lower := (rows 7 42 196 265 112 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 20 173 64 129 257), good := (rows 445 40 244 425 112 160 64 160 256) }] }

theorem u1913 : Upper (D 7) (R 7) [6,40,192,257,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 42 196 265 112 160 80 131 259), lower := (rows 7 42 196 265 112 160 80 128 256), losses := [] }

theorem u1914 : Upper (D 7) (R 7) [6,40,192,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1914 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(3,0)], upper := (rows 7 42 196 266 112 33 65 144 400), lower := (rows 7 42 196 266 112 33 65 128 256), losses := [] }

theorem u1915 : Upper (D 7) (R 7) [6,40,192,258,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 266 112 33 80 129 385), lower := (rows 7 42 196 266 112 33 80 128 256), losses := [] }

theorem u1916 : Upper (D 7) (R 7) [6,40,192,258,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1916 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 266 112 33 192 145 273), lower := (rows 7 42 196 266 112 33 192 128 256), losses := [] }

theorem u1917 : Upper (D 7) (R 7) [6,40,192,258,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1918 : Route 9 := (fun mask => (mask,id))

def c1918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1918 : Upper (D 7) (R 7) [6,40,192,258,96,128,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,96,128,1] 13 (by decide) (choices 1) [1,16] r1918 c1918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u92
  · exact u93

def b1919 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 42 196 266 112 160 80 129 257), lower := (rows 7 42 196 266 112 160 80 128 256), losses := [] }

theorem u1919 : Upper (D 7) (R 7) [6,40,192,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1919 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P07
