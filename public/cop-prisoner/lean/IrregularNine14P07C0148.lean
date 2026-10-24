import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8880 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 160 },{ cop := 4, region := 162, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,5),(4,7)], upper := (rows 37 194 268 11 81 160 66 176 304), lower := (rows 37 194 268 11 81 160 66 128 256), losses := [] }

theorem u8880 : Upper (D 7) (R 7) [36,192,264,3,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8881 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 194 268 11 81 160 80 162 290), lower := (rows 37 194 268 11 81 160 80 128 256), losses := [] }

theorem u8881 : Upper (D 7) (R 7) [36,192,264,3,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8881 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8882 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 268 11 81 160 96 146 274), lower := (rows 37 194 268 11 81 160 96 128 256), losses := [] }

theorem u8882 : Upper (D 7) (R 7) [36,192,264,3,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8883 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 6, region := 178, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 37 194 268 11 112 160 65 146 274), lower := (rows 37 194 268 11 112 160 65 128 256), losses := [] }

theorem u8883 : Upper (D 7) (R 7) [36,192,264,3,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8883 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8884 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 1, region := 48, targets := 2 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 37 194 268 11 112 160 66 145 273), lower := (rows 37 194 268 11 112 160 66 128 256), losses := [] }

theorem u8884 : Upper (D 7) (R 7) [36,192,264,3,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8885 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 194 268 11 112 160 80 131 259), lower := (rows 37 194 268 11 112 160 80 128 256), losses := [] }

theorem u8885 : Upper (D 7) (R 7) [36,192,264,3,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8885 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8886 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 194 268 26 81 160 65 162 290), lower := (rows 37 194 268 26 81 160 65 128 256), losses := [] }

theorem u8886 : Upper (D 7) (R 7) [36,192,264,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8887 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 268 26 81 160 66 161 289), lower := (rows 37 194 268 26 81 160 66 128 256), losses := [] }

theorem u8887 : Upper (D 7) (R 7) [36,192,264,18,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8887 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8888 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 268 26 81 160 96 131 259), lower := (rows 37 194 268 26 81 160 96 128 256), losses := [] }

theorem u8888 : Upper (D 7) (R 7) [36,192,264,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8889 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 194 268 56 81 34 65 130 386), lower := (rows 37 194 268 56 81 34 65 128 256), losses := [] }

theorem u8889 : Upper (D 7) (R 7) [36,192,264,48,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8889 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8890 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 389, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 268 56 81 34 66 129 385), lower := (rows 37 194 268 56 81 34 66 128 256), losses := [] }

theorem u8890 : Upper (D 7) (R 7) [36,192,264,48,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8891 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 268 56 81 34 192 131 259), lower := (rows 37 194 268 56 81 34 192 128 256), losses := [] }

theorem u8891 : Upper (D 7) (R 7) [36,192,264,48,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8892 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 194 268 56 81 160 65 130 258), lower := (rows 37 194 268 56 81 160 65 128 256), losses := [] }

theorem u8892 : Upper (D 7) (R 7) [36,192,264,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8892 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8893 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5),(4,5)], upper := (rows 37 194 268 56 81 160 66 131 259), lower := (rows 37 194 268 56 81 160 66 128 256), losses := [{ target := 5, region := (rows 1 187 12 8 17 0 255 145 273), good := (rows 471 194 334 478 467 194 66 194 256) }] }

theorem u8893 : Upper (D 7) (R 7) [36,192,264,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8894 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 37 194 268 73 19 34 80 160 416), lower := (rows 37 194 268 73 19 34 80 128 256), losses := [] }

theorem u8894 : Upper (D 7) (R 7) [36,192,264,65,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8894 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8895 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 268 73 19 34 96 144 400), lower := (rows 37 194 268 73 19 34 96 128 256), losses := [] }

theorem u8895 : Upper (D 7) (R 7) [36,192,264,65,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8896 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 268 73 19 34 192 176 304), lower := (rows 37 194 268 73 19 34 192 128 256), losses := [] }

theorem u8896 : Upper (D 7) (R 7) [36,192,264,65,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8897 : PairBound 9 := { available := 160, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 4, region := 72, targets := 32 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 37 194 268 73 19 48 66 160 416), lower := (rows 37 194 268 73 19 48 66 128 256), losses := [] }

theorem u8897 : Upper (D 7) (R 7) [36,192,264,65,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8897 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8898 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 268 73 19 48 96 130 386), lower := (rows 37 194 268 73 19 48 96 128 256), losses := [] }

theorem u8898 : Upper (D 7) (R 7) [36,192,264,65,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8898 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8899 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 268 73 19 48 192 162 290), lower := (rows 37 194 268 73 19 48 192 128 256), losses := [] }

theorem u8899 : Upper (D 7) (R 7) [36,192,264,65,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8899 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8900 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 72, targets := 160 },{ cop := 4, region := 226, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,5),(3,7)], upper := (rows 37 194 268 73 19 160 66 176 304), lower := (rows 37 194 268 73 19 160 66 128 256), losses := [] }

theorem u8900 : Upper (D 7) (R 7) [36,192,264,65,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8901 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 194 268 73 19 160 80 162 290), lower := (rows 37 194 268 73 19 160 80 128 256), losses := [] }

theorem u8901 : Upper (D 7) (R 7) [36,192,264,65,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8901 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8902 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 268 73 19 160 96 146 274), lower := (rows 37 194 268 73 19 160 96 128 256), losses := [] }

theorem u8902 : Upper (D 7) (R 7) [36,192,264,65,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8903 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 194 268 73 145 34 66 176 304), lower := (rows 37 194 268 73 145 34 66 128 256), losses := [] }

theorem u8903 : Upper (D 7) (R 7) [36,192,264,65,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8904 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 268 73 145 34 80 162 290), lower := (rows 37 194 268 73 145 34 80 128 256), losses := [] }

theorem u8904 : Upper (D 7) (R 7) [36,192,264,65,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8904 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8905 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 268 73 145 34 96 146 274), lower := (rows 37 194 268 73 145 34 96 128 256), losses := [] }

theorem u8905 : Upper (D 7) (R 7) [36,192,264,65,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8906 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 74, targets := 32 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 37 194 268 73 145 48 66 162 290), lower := (rows 37 194 268 73 145 48 66 128 256), losses := [] }

theorem u8906 : Upper (D 7) (R 7) [36,192,264,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8906 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8907 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 268 73 145 48 96 130 258), lower := (rows 37 194 268 73 145 48 96 128 256), losses := [] }

theorem u8907 : Upper (D 7) (R 7) [36,192,264,65,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8907 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8908 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 268 73 176 34 65 146 274), lower := (rows 37 194 268 73 176 34 65 128 256), losses := [] }

theorem u8908 : Upper (D 7) (R 7) [36,192,264,65,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8909 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 7, region := 114, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,6)], upper := (rows 37 194 268 73 176 34 66 145 273), lower := (rows 37 194 268 73 176 34 66 128 256), losses := [] }

theorem u8909 : Upper (D 7) (R 7) [36,192,264,65,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8910 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 268 73 176 34 80 131 259), lower := (rows 37 194 268 73 176 34 80 128 256), losses := [] }

theorem u8910 : Upper (D 7) (R 7) [36,192,264,65,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8910 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8911 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 268 88 19 160 65 162 290), lower := (rows 37 194 268 88 19 160 65 128 256), losses := [] }

theorem u8911 : Upper (D 7) (R 7) [36,192,264,80,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8912 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 268 88 19 160 66 161 289), lower := (rows 37 194 268 88 19 160 66 128 256), losses := [] }

theorem u8912 : Upper (D 7) (R 7) [36,192,264,80,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8913 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(3,1)], upper := (rows 37 194 268 88 19 160 96 131 259), lower := (rows 37 194 268 88 19 160 96 128 256), losses := [{ target := 0, region := (rows 0 162 4 24 16 162 243 128 256), good := (rows 102 226 268 88 122 226 98 226 256) },{ target := 1, region := (rows 1 0 4 24 16 162 243 128 256), good := (rows 101 224 268 88 121 224 96 224 256) },{ target := 5, region := (rows 1 10 12 8 16 0 64 144 272), good := (rows 5 194 270 478 403 128 64 128 256) }] }

theorem u8913 : Upper (D 7) (R 7) [36,192,264,80,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8914 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 130 }], pairs := [(1,0),(2,0),(3,1),(3,7)], upper := (rows 37 194 268 88 145 34 65 162 290), lower := (rows 37 194 268 88 145 34 65 128 256), losses := [] }

theorem u8914 : Upper (D 7) (R 7) [36,192,264,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8915 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 37 194 268 88 145 34 66 161 289), lower := (rows 37 194 268 88 145 34 66 128 256), losses := [] }

theorem u8915 : Upper (D 7) (R 7) [36,192,264,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8916 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,7)], upper := (rows 37 194 268 88 145 34 96 131 259), lower := (rows 37 194 268 88 145 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 32 97 128 256), good := (rows 101 192 268 88 217 96 96 128 256) },{ target := 7, region := (rows 1 2 4 24 16 34 99 0 256), good := (rows 101 98 268 88 89 98 96 0 256) }] }

theorem u8916 : Upper (D 7) (R 7) [36,192,264,80,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8917 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 268 104 19 48 65 130 386), lower := (rows 37 194 268 104 19 48 65 128 256), losses := [] }

theorem u8917 : Upper (D 7) (R 7) [36,192,264,96,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8917 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8918 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 389, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 194 268 104 19 48 66 129 385), lower := (rows 37 194 268 104 19 48 66 128 256), losses := [] }

theorem u8918 : Upper (D 7) (R 7) [36,192,264,96,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8918 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8919 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 268 104 19 48 192 131 259), lower := (rows 37 194 268 104 19 48 192 128 256), losses := [] }

theorem u8919 : Upper (D 7) (R 7) [36,192,264,96,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8920 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 268 104 145 48 65 130 258), lower := (rows 37 194 268 104 145 48 65 128 256), losses := [] }

theorem u8920 : Upper (D 7) (R 7) [36,192,264,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8920 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8921 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 37 194 268 104 145 48 66 131 259), lower := (rows 37 194 268 104 145 48 66 128 256), losses := [] }

theorem u8921 : Upper (D 7) (R 7) [36,192,264,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8921 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8922 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 176, targets := 65 }], pairs := [(1,5),(4,0),(4,1),(4,6)], upper := (rows 37 194 324 11 56 160 65 146 274), lower := (rows 37 194 324 11 56 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 162 73 128 256), good := (rows 101 224 324 121 120 160 65 160 256) },{ target := 5, region := (rows 1 18 20 8 16 0 73 144 272), good := (rows 69 194 324 75 478 128 65 128 256) }] }

theorem u8922 : Upper (D 7) (R 7) [36,192,320,3,40,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8923 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 176, targets := 66 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 194 324 11 56 160 66 145 273), lower := (rows 37 194 324 11 56 160 66 128 256), losses := [] }

theorem u8923 : Upper (D 7) (R 7) [36,192,320,3,40,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8924 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 324 11 56 160 80 131 259), lower := (rows 37 194 324 11 56 160 80 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 162 88 128 256), good := (rows 36 226 324 122 120 160 80 160 256) },{ target := 1, region := (rows 1 0 4 8 24 162 88 128 256), good := (rows 37 224 324 121 120 160 80 160 256) }] }

theorem u8924 : Upper (D 7) (R 7) [36,192,320,3,40,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8924 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8925 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 37 194 324 11 145 34 72 176 304), lower := (rows 37 194 324 11 145 34 72 128 256), losses := [] }

theorem u8925 : Upper (D 7) (R 7) [36,192,320,3,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8925 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8926 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 11 145 34 80 168 296), lower := (rows 37 194 324 11 145 34 80 128 256), losses := [] }

theorem u8926 : Upper (D 7) (R 7) [36,192,320,3,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8926 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8927 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 144, targets := 34 },{ cop := 3, region := 144, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 37 194 324 11 145 34 96 152 280), lower := (rows 37 194 324 11 145 34 96 128 256), losses := [] }

theorem u8927 : Upper (D 7) (R 7) [36,192,320,3,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8927 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8928 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 37 194 324 11 145 40 66 176 304), lower := (rows 37 194 324 11 145 40 66 128 256), losses := [] }

theorem u8928 : Upper (D 7) (R 7) [36,192,320,3,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8928 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8929 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 324 11 145 40 80 162 290), lower := (rows 37 194 324 11 145 40 80 128 256), losses := [] }

theorem u8929 : Upper (D 7) (R 7) [36,192,320,3,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8929 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8930 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 144, targets := 32 },{ cop := 3, region := 144, targets := 64 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 194 324 11 145 40 96 146 274), lower := (rows 37 194 324 11 145 40 96 128 256), losses := [{ target := 0, region := (rows 0 18 20 8 16 40 105 144 272), good := (rows 100 194 324 106 470 104 96 128 256) }] }

theorem u8930 : Upper (D 7) (R 7) [36,192,320,3,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8930 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8931 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 176, targets := 66 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 37 194 324 11 145 48 66 168 296), lower := (rows 37 194 324 11 145 48 66 128 256), losses := [] }

theorem u8931 : Upper (D 7) (R 7) [36,192,320,3,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8931 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8932 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 74, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 37 194 324 11 145 48 72 162 290), lower := (rows 37 194 324 11 145 48 72 128 256), losses := [] }

theorem u8932 : Upper (D 7) (R 7) [36,192,320,3,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8932 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8933 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 144, targets := 32 },{ cop := 3, region := 144, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 194 324 11 145 48 96 138 266), lower := (rows 37 194 324 11 145 48 96 128 256), losses := [] }

theorem u8933 : Upper (D 7) (R 7) [36,192,320,3,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8933 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8934 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 176, targets := 65 }], pairs := [(0,7),(1,5),(4,0),(4,6)], upper := (rows 37 194 324 11 152 34 65 176 304), lower := (rows 37 194 324 11 152 34 65 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 73 128 256), good := (rows 69 194 324 75 218 2 65 128 256) },{ target := 7, region := (rows 17 2 20 8 16 42 89 0 272), good := (rows 101 98 324 107 381 34 65 0 256) }] }

theorem u8934 : Upper (D 7) (R 7) [36,192,320,3,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8935 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 11 152 34 80 161 289), lower := (rows 37 194 324 11 152 34 80 128 256), losses := [] }

theorem u8935 : Upper (D 7) (R 7) [36,192,320,3,136,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8935 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8936 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 144, targets := 34 },{ cop := 3, region := 144, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,6)], upper := (rows 37 194 324 11 152 34 96 145 273), lower := (rows 37 194 324 11 152 34 96 128 256), losses := [] }

theorem u8936 : Upper (D 7) (R 7) [36,192,320,3,136,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8937 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 176, targets := 65 }], pairs := [(1,5),(4,0),(4,6)], upper := (rows 37 194 324 11 152 48 65 162 290), lower := (rows 37 194 324 11 152 48 65 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 73 128 256), good := (rows 69 194 324 75 218 18 65 128 256) }] }

theorem u8937 : Upper (D 7) (R 7) [36,192,320,3,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8937 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8938 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 176, targets := 66 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 37 194 324 11 152 48 66 161 289), lower := (rows 37 194 324 11 152 48 66 128 256), losses := [] }

theorem u8938 : Upper (D 7) (R 7) [36,192,320,3,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8938 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8939 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 144, targets := 32 },{ cop := 3, region := 144, targets := 64 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 194 324 11 152 48 96 131 259), lower := (rows 37 194 324 11 152 48 96 128 256), losses := [] }

theorem u8939 : Upper (D 7) (R 7) [36,192,320,3,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8939 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8939
end Delivery.IrregularNine14.P07
