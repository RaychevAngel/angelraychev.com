import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5880 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 76 280 48 68 162 290), lower := (rows 35 67 133 76 280 48 68 128 256), losses := [] }

theorem u5880 : Upper (D 6) (R 6) [34,65,129,68,264,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5880 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5881 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 140, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 133 76 280 48 96 134 262), lower := (rows 35 67 133 76 280 48 96 128 256), losses := [] }

theorem u5881 : Upper (D 6) (R 6) [34,65,129,68,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5881 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5882 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 76 304 36 66 152 280), lower := (rows 35 67 133 76 304 36 66 128 256), losses := [] }

theorem u5882 : Upper (D 6) (R 6) [34,65,129,68,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5883 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 76 304 36 72 146 274), lower := (rows 35 67 133 76 304 36 72 128 256), losses := [] }

theorem u5883 : Upper (D 6) (R 6) [34,65,129,68,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5883 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5884 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 140, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 133 76 304 36 80 138 266), lower := (rows 35 67 133 76 304 36 80 128 256), losses := [] }

theorem u5884 : Upper (D 6) (R 6) [34,65,129,68,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5884 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5885 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 133 88 274 36 68 168 296), lower := (rows 35 67 133 88 274 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 15 19 100 100 239 367), good := (rows 506 506 508 504 410 492 492 128 256) }] }

theorem u5885 : Upper (D 6) (R 6) [34,65,129,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5886 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 67 133 88 274 36 72 164 292), lower := (rows 35 67 133 88 274 36 72 128 256), losses := [] }

theorem u5886 : Upper (D 6) (R 6) [34,65,129,80,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5886 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5887 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 88 274 36 96 140 268), lower := (rows 35 67 133 88 274 36 96 128 256), losses := [] }

theorem u5887 : Upper (D 6) (R 6) [34,65,129,80,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5888 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 88 276 36 66 168 296), lower := (rows 35 67 133 88 276 36 66 128 256), losses := [] }

theorem u5888 : Upper (D 6) (R 6) [34,65,129,80,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5889 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 88 276 36 72 162 290), lower := (rows 35 67 133 88 276 36 72 128 256), losses := [] }

theorem u5889 : Upper (D 6) (R 6) [34,65,129,80,260,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5889 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5890 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 88 276 36 96 138 266), lower := (rows 35 67 133 88 276 36 96 128 256), losses := [] }

theorem u5890 : Upper (D 6) (R 6) [34,65,129,80,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5891 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 88 280 36 66 164 292), lower := (rows 35 67 133 88 280 36 66 128 256), losses := [] }

theorem u5891 : Upper (D 6) (R 6) [34,65,129,80,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5892 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 66, targets := 32 }], pairs := [(0,6),(1,5),(2,6)], upper := (rows 35 67 133 88 280 36 68 162 290), lower := (rows 35 67 133 88 280 36 68 128 256), losses := [] }

theorem u5892 : Upper (D 6) (R 6) [34,65,129,80,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5893 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 133 88 280 36 96 134 262), lower := (rows 35 67 133 88 280 36 96 128 256), losses := [] }

theorem u5893 : Upper (D 6) (R 6) [34,65,129,80,264,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5894 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 88 304 36 66 140 268), lower := (rows 35 67 133 88 304 36 66 128 256), losses := [] }

theorem u5894 : Upper (D 6) (R 6) [34,65,129,80,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5895 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 133 88 304 36 68 138 266), lower := (rows 35 67 133 88 304 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 127 23 100 100 131 259), good := (rows 506 506 508 120 376 124 124 128 256) }] }

theorem u5895 : Upper (D 6) (R 6) [34,65,129,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5896 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 88 304 36 72 134 262), lower := (rows 35 67 133 88 304 36 72 128 256), losses := [] }

theorem u5896 : Upper (D 6) (R 6) [34,65,129,80,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5896 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5897 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 275, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 133 104 274 36 68 152 280), lower := (rows 35 67 133 104 274 36 68 128 256), losses := [] }

theorem u5897 : Upper (D 6) (R 6) [34,65,129,96,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5898 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 104 274 36 72 148 276), lower := (rows 35 67 133 104 274 36 72 128 256), losses := [] }

theorem u5898 : Upper (D 6) (R 6) [34,65,129,96,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5898 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5899 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 172, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 133 104 274 36 80 140 268), lower := (rows 35 67 133 104 274 36 80 128 256), losses := [] }

theorem u5899 : Upper (D 6) (R 6) [34,65,129,96,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5899 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5900 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 104 276 36 66 152 280), lower := (rows 35 67 133 104 276 36 66 128 256), losses := [] }

theorem u5900 : Upper (D 6) (R 6) [34,65,129,96,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5901 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 104 276 36 72 146 274), lower := (rows 35 67 133 104 276 36 72 128 256), losses := [] }

theorem u5901 : Upper (D 6) (R 6) [34,65,129,96,260,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5901 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5902 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 104 276 36 80 138 266), lower := (rows 35 67 133 104 276 36 80 128 256), losses := [] }

theorem u5902 : Upper (D 6) (R 6) [34,65,129,96,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5902 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5903 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 104 280 36 66 148 276), lower := (rows 35 67 133 104 280 36 66 128 256), losses := [] }

theorem u5903 : Upper (D 6) (R 6) [34,65,129,96,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5904 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 275, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 67 133 104 280 36 68 146 274), lower := (rows 35 67 133 104 280 36 68 128 256), losses := [] }

theorem u5904 : Upper (D 6) (R 6) [34,65,129,96,264,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5905 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 104 280 36 80 134 262), lower := (rows 35 67 133 104 280 36 80 128 256), losses := [] }

theorem u5905 : Upper (D 6) (R 6) [34,65,129,96,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5905 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5906 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 25 84 288 66 164 292), lower := (rows 35 67 140 25 84 288 66 128 256), losses := [] }

theorem u5906 : Upper (D 6) (R 6) [34,65,136,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5906 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5907 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 25 84 288 68 162 290), lower := (rows 35 67 140 25 84 288 68 128 256), losses := [] }

theorem u5907 : Upper (D 6) (R 6) [34,65,136,17,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5907 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5908 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 140 25 84 288 96 134 262), lower := (rows 35 67 140 25 84 288 96 128 256), losses := [] }

theorem u5908 : Upper (D 6) (R 6) [34,65,136,17,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5908 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5909 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 304 36 66 196 324), lower := (rows 35 67 140 25 304 36 66 128 256), losses := [] }

theorem u5909 : Upper (D 6) (R 6) [34,65,136,17,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5910 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,0),(2,5)], upper := (rows 35 67 140 25 304 36 68 194 322), lower := (rows 35 67 140 25 304 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 108 108 131 259), good := (rows 498 498 252 508 368 100 100 128 256) }] }

theorem u5910 : Upper (D 6) (R 6) [34,65,136,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5911 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 25 336 36 66 164 292), lower := (rows 35 67 140 25 336 36 66 128 256), losses := [] }

theorem u5911 : Upper (D 6) (R 6) [34,65,136,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5912 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(3,2),(4,0)], upper := (rows 35 67 140 25 336 36 68 162 290), lower := (rows 35 67 140 25 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 108 108 131 259), good := (rows 498 498 252 508 368 100 100 128 256) },{ target := 2, region := (rows 1 2 0 11 18 32 64 129 257), good := (rows 443 475 136 409 336 32 64 128 256) }] }

theorem u5912 : Upper (D 6) (R 6) [34,65,136,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5913 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 140 25 336 36 96 134 262), lower := (rows 35 67 140 25 336 36 96 128 256), losses := [] }

theorem u5913 : Upper (D 6) (R 6) [34,65,136,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5914 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 56 22 288 65 196 324), lower := (rows 35 67 140 56 22 288 65 128 256), losses := [] }

theorem u5914 : Upper (D 6) (R 6) [34,65,136,48,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5914 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5915 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 56 22 288 68 193 321), lower := (rows 35 67 140 56 22 288 68 128 256), losses := [] }

theorem u5915 : Upper (D 6) (R 6) [34,65,136,48,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5915 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5916 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 56 84 288 65 134 262), lower := (rows 35 67 140 56 84 288 65 128 256), losses := [] }

theorem u5916 : Upper (D 6) (R 6) [34,65,136,48,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5916 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5917 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 56 84 288 66 133 261), lower := (rows 35 67 140 56 84 288 66 128 256), losses := [] }

theorem u5917 : Upper (D 6) (R 6) [34,65,136,48,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5917 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5918 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 140 56 84 288 68 131 259), lower := (rows 35 67 140 56 84 288 68 128 256), losses := [] }

theorem u5918 : Upper (D 6) (R 6) [34,65,136,48,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5918 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5919 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 273 36 66 196 324), lower := (rows 35 67 140 56 273 36 66 128 256), losses := [] }

theorem u5919 : Upper (D 6) (R 6) [34,65,136,48,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5920 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 36 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 67 140 56 273 36 68 194 322), lower := (rows 35 67 140 56 273 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 124 124 131 259), good := (rows 482 482 236 124 508 100 100 128 256) }] }

theorem u5920 : Upper (D 6) (R 6) [34,65,136,48,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5921 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 56 274 36 65 196 324), lower := (rows 35 67 140 56 274 36 65 128 256), losses := [] }

theorem u5921 : Upper (D 6) (R 6) [34,65,136,48,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5922 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 272, targets := 36 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 35 67 140 56 274 36 68 193 321), lower := (rows 35 67 140 56 274 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 124 124 131 259), good := (rows 481 481 236 124 508 100 100 128 256) }] }

theorem u5922 : Upper (D 6) (R 6) [34,65,136,48,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5923 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 56 336 36 65 134 262), lower := (rows 35 67 140 56 336 36 65 128 256), losses := [] }

theorem u5923 : Upper (D 6) (R 6) [34,65,136,48,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5924 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 56 336 36 66 133 261), lower := (rows 35 67 140 56 336 36 66 128 256), losses := [] }

theorem u5924 : Upper (D 6) (R 6) [34,65,136,48,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5925 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 36 }], pairs := [(3,0),(4,2),(4,5)], upper := (rows 35 67 140 56 336 36 68 131 259), lower := (rows 35 67 140 56 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 128 256), good := (rows 98 98 236 120 376 100 100 128 256) }] }

theorem u5925 : Upper (D 6) (R 6) [34,65,136,48,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5926 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 104 273 36 66 148 276), lower := (rows 35 67 140 104 273 36 66 128 256), losses := [] }

theorem u5926 : Upper (D 6) (R 6) [34,65,136,96,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5927 : PairBound 9 := { available := 18, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 140 104 273 36 68 146 274), lower := (rows 35 67 140 104 273 36 68 128 256), losses := [] }

theorem u5927 : Upper (D 6) (R 6) [34,65,136,96,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5928 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 172, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 140 104 273 36 80 134 262), lower := (rows 35 67 140 104 273 36 80 128 256), losses := [] }

theorem u5928 : Upper (D 6) (R 6) [34,65,136,96,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5928 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5929 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 140 104 276 33 68 146 274), lower := (rows 35 67 140 104 276 33 68 128 256), losses := [] }

theorem u5929 : Upper (D 6) (R 6) [34,65,136,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5930 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 104 276 34 68 145 273), lower := (rows 35 67 140 104 276 34 68 128 256), losses := [] }

theorem u5930 : Upper (D 6) (R 6) [34,65,136,96,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5931 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 140 104 276 36 80 131 259), lower := (rows 35 67 140 104 276 36 80 128 256), losses := [] }

theorem u5931 : Upper (D 6) (R 6) [34,65,136,96,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5931 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5932 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 140 265 22 36 80 224 352), lower := (rows 35 67 140 265 22 36 80 128 256), losses := [] }

theorem u5932 : Upper (D 6) (R 6) [34,65,136,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5932 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5933 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 140 265 22 36 96 208 336), lower := (rows 35 67 140 265 22 36 96 128 256), losses := [] }

theorem u5933 : Upper (D 6) (R 6) [34,65,136,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5934 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 84 36 66 176 304), lower := (rows 35 67 140 265 84 36 66 128 256), losses := [] }

theorem u5934 : Upper (D 6) (R 6) [34,65,136,257,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5935 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 140 265 84 36 80 162 290), lower := (rows 35 67 140 265 84 36 80 128 256), losses := [] }

theorem u5935 : Upper (D 6) (R 6) [34,65,136,257,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5935 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5936 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 140 265 84 36 96 146 274), lower := (rows 35 67 140 265 84 36 96 128 256), losses := [] }

theorem u5936 : Upper (D 6) (R 6) [34,65,136,257,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5937 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 140 265 112 36 66 148 276), lower := (rows 35 67 140 265 112 36 66 128 256), losses := [] }

theorem u5937 : Upper (D 6) (R 6) [34,65,136,257,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5938 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 67 140 265 112 36 68 146 274), lower := (rows 35 67 140 265 112 36 68 128 256), losses := [] }

theorem u5938 : Upper (D 6) (R 6) [34,65,136,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5939 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 140 265 112 36 80 134 262), lower := (rows 35 67 140 265 112 36 80 128 256), losses := [] }

theorem u5939 : Upper (D 6) (R 6) [34,65,136,257,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5939 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5939
end Delivery.IrregularNine14.P06
