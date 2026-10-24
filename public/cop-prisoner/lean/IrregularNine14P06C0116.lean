import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0008

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6960 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 131 324 14 81 36 72 176 304), lower := (rows 35 131 324 14 81 36 72 128 256), losses := [] }

theorem u6960 : Upper (D 6) (R 6) [34,129,320,6,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6960 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6961 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 131 324 14 81 36 80 168 296), lower := (rows 35 131 324 14 81 36 80 128 256), losses := [] }

theorem u6961 : Upper (D 6) (R 6) [34,129,320,6,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6961 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6962 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 324 14 81 36 96 152 280), lower := (rows 35 131 324 14 81 36 96 128 256), losses := [] }

theorem u6962 : Upper (D 6) (R 6) [34,129,320,6,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6963 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 292, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 131 324 14 88 36 65 176 304), lower := (rows 35 131 324 14 88 36 65 128 256), losses := [] }

theorem u6963 : Upper (D 6) (R 6) [34,129,320,6,72,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6964 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 324 14 88 36 80 161 289), lower := (rows 35 131 324 14 88 36 80 128 256), losses := [] }

theorem u6964 : Upper (D 6) (R 6) [34,129,320,6,72,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6964 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6965 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 35 131 324 14 88 36 96 145 273), lower := (rows 35 131 324 14 88 36 96 128 256), losses := [] }

theorem u6965 : Upper (D 6) (R 6) [34,129,320,6,72,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6966 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 131 324 14 88 48 65 164 292), lower := (rows 35 131 324 14 88 48 65 128 256), losses := [] }

theorem u6966 : Upper (D 6) (R 6) [34,129,320,6,72,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6966 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6967 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 163, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 14 88 48 68 161 289), lower := (rows 35 131 324 14 88 48 68 128 256), losses := [] }

theorem u6967 : Upper (D 6) (R 6) [34,129,320,6,72,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6967 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6968 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 131 324 14 88 48 96 133 261), lower := (rows 35 131 324 14 88 48 96 128 256), losses := [] }

theorem u6968 : Upper (D 6) (R 6) [34,129,320,6,72,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6968 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6969 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 324 25 28 96 66 164 292), lower := (rows 35 131 324 25 28 96 66 128 256), losses := [] }

theorem u6969 : Upper (D 6) (R 6) [34,129,320,17,12,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6970 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 25 28 96 68 162 290), lower := (rows 35 131 324 25 28 96 68 128 256), losses := [] }

theorem u6970 : Upper (D 6) (R 6) [34,129,320,17,12,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6971 : PairBound 9 := { available := 6, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 324 25 28 96 96 134 262), lower := (rows 35 131 324 25 28 96 96 128 256), losses := [] }

theorem u6971 : Upper (D 6) (R 6) [34,129,320,17,12,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6972 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 8, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 324 25 82 36 68 168 296), lower := (rows 35 131 324 25 82 36 68 128 256), losses := [] }

theorem u6972 : Upper (D 6) (R 6) [34,129,320,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6973 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 131 324 25 82 36 72 164 292), lower := (rows 35 131 324 25 82 36 72 128 256), losses := [] }

theorem u6973 : Upper (D 6) (R 6) [34,129,320,17,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6973 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6974 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 356, targets := 1 }], pairs := [(2,0),(3,2),(4,2)], upper := (rows 35 131 324 25 82 36 96 140 268), lower := (rows 35 131 324 25 82 36 96 128 256), losses := [] }

theorem u6974 : Upper (D 6) (R 6) [34,129,320,17,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6975 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 260, targets := 3 },{ cop := 7, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(2,1)], upper := (rows 35 131 324 26 28 96 65 164 292), lower := (rows 35 131 324 26 28 96 65 128 256), losses := [] }

theorem u6975 : Upper (D 6) (R 6) [34,129,320,18,12,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6976 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 26 28 96 68 161 289), lower := (rows 35 131 324 26 28 96 68 128 256), losses := [] }

theorem u6976 : Upper (D 6) (R 6) [34,129,320,18,12,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6977 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 99, targets := 4 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 131 324 26 28 96 96 133 261), lower := (rows 35 131 324 26 28 96 96 128 256), losses := [] }

theorem u6977 : Upper (D 6) (R 6) [34,129,320,18,12,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6978 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 356, targets := 3 },{ cop := 8, region := 68, targets := 32 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 131 324 26 81 36 68 168 296), lower := (rows 35 131 324 26 81 36 68 128 256), losses := [] }

theorem u6978 : Upper (D 6) (R 6) [34,129,320,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6979 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 131 324 26 81 36 72 164 292), lower := (rows 35 131 324 26 81 36 72 128 256), losses := [] }

theorem u6979 : Upper (D 6) (R 6) [34,129,320,18,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6979 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6980 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 324 26 81 36 96 140 268), lower := (rows 35 131 324 26 81 36 96 128 256), losses := [] }

theorem u6980 : Upper (D 6) (R 6) [34,129,320,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6981 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 35 131 324 26 112 36 65 140 268), lower := (rows 35 131 324 26 112 36 65 128 256), losses := [] }

theorem u6981 : Upper (D 6) (R 6) [34,129,320,18,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6982 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 139, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 26 112 36 68 137 265), lower := (rows 35 131 324 26 112 36 68 128 256), losses := [] }

theorem u6982 : Upper (D 6) (R 6) [34,129,320,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6983 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 131 324 26 112 36 72 133 261), lower := (rows 35 131 324 26 112 36 72 128 256), losses := [] }

theorem u6983 : Upper (D 6) (R 6) [34,129,320,18,96,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6983 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6984 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 324 28 81 36 66 168 296), lower := (rows 35 131 324 28 81 36 66 128 256), losses := [] }

theorem u6984 : Upper (D 6) (R 6) [34,129,320,20,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6985 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 28 81 36 72 162 290), lower := (rows 35 131 324 28 81 36 72 128 256), losses := [] }

theorem u6985 : Upper (D 6) (R 6) [34,129,320,20,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6985 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6986 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 131 324 28 81 36 96 138 266), lower := (rows 35 131 324 28 81 36 96 128 256), losses := [] }

theorem u6986 : Upper (D 6) (R 6) [34,129,320,20,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6987 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 324 28 82 36 65 168 296), lower := (rows 35 131 324 28 82 36 65 128 256), losses := [] }

theorem u6987 : Upper (D 6) (R 6) [34,129,320,20,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6988 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 324 28 82 36 72 161 289), lower := (rows 35 131 324 28 82 36 72 128 256), losses := [] }

theorem u6988 : Upper (D 6) (R 6) [34,129,320,20,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6988 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6989 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 8, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 324 28 82 36 96 137 265), lower := (rows 35 131 324 28 82 36 96 128 256), losses := [] }

theorem u6989 : Upper (D 6) (R 6) [34,129,320,20,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6990 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 324 56 81 36 66 140 268), lower := (rows 35 131 324 56 81 36 66 128 256), losses := [] }

theorem u6990 : Upper (D 6) (R 6) [34,129,320,48,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6991 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 56 81 36 68 138 266), lower := (rows 35 131 324 56 81 36 68 128 256), losses := [] }

theorem u6991 : Upper (D 6) (R 6) [34,129,320,48,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6992 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 324 56 81 36 72 134 262), lower := (rows 35 131 324 56 81 36 72 128 256), losses := [] }

theorem u6992 : Upper (D 6) (R 6) [34,129,320,48,65,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6992 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6993 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 300, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 324 56 82 36 65 140 268), lower := (rows 35 131 324 56 82 36 65 128 256), losses := [] }

theorem u6993 : Upper (D 6) (R 6) [34,129,320,48,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6994 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 131, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 131 324 56 82 36 68 137 265), lower := (rows 35 131 324 56 82 36 68 128 256), losses := [] }

theorem u6994 : Upper (D 6) (R 6) [34,129,320,48,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6995 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 131 324 56 82 36 72 133 261), lower := (rows 35 131 324 56 82 36 72 128 256), losses := [] }

theorem u6995 : Upper (D 6) (R 6) [34,129,320,48,66,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6995 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6996 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 25 82 288 65 196 324), lower := (rows 35 134 44 25 82 288 65 128 256), losses := [] }

theorem u6996 : Upper (D 6) (R 6) [34,132,40,17,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6996 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6997 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 134 44 25 82 288 68 193 321), lower := (rows 35 134 44 25 82 288 68 128 256), losses := [] }

theorem u6997 : Upper (D 6) (R 6) [34,132,40,17,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6997 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6998 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 44 25 84 288 65 194 322), lower := (rows 35 134 44 25 84 288 65 128 256), losses := [] }

theorem u6998 : Upper (D 6) (R 6) [34,132,40,17,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6998 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6999 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 134 44 25 84 288 66 193 321), lower := (rows 35 134 44 25 84 288 66 128 256), losses := [] }

theorem u6999 : Upper (D 6) (R 6) [34,132,40,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6999 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7000 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 4 },{ cop := 3, region := 100, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 134 44 25 274 96 65 196 324), lower := (rows 35 134 44 25 274 96 65 128 256), losses := [] }

theorem u7000 : Upper (D 6) (R 6) [34,132,40,17,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7000 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7001 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 100, targets := 1 },{ cop := 3, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(3,5)], upper := (rows 35 134 44 25 274 96 68 193 321), lower := (rows 35 134 44 25 274 96 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 70 129 257), good := (rows 475 198 76 409 338 64 68 128 256) }] }

theorem u7001 : Upper (D 6) (R 6) [34,132,40,17,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7001 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7002 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 3, region := 100, targets := 2 }], pairs := [(0,2),(1,5),(2,1)], upper := (rows 35 134 44 25 276 96 65 194 322), lower := (rows 35 134 44 25 276 96 65 128 256), losses := [{ target := 5, region := (rows 1 22 4 9 22 0 73 141 269), good := (rows 475 406 478 475 406 64 457 128 256) }] }

theorem u7002 : Upper (D 6) (R 6) [34,132,40,17,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7002 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7003 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,0)], upper := (rows 35 134 44 25 276 96 66 193 321), lower := (rows 35 134 44 25 276 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 107 67 128 256), good := (rows 98 230 44 124 276 96 98 128 256) },{ target := 5, region := (rows 1 6 4 8 20 0 87 137 265), good := (rows 451 214 478 473 342 64 66 128 256) }] }

theorem u7003 : Upper (D 6) (R 6) [34,132,40,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7003 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7004 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 26 81 288 65 196 324), lower := (rows 35 134 44 26 81 288 65 128 256), losses := [] }

theorem u7004 : Upper (D 6) (R 6) [34,132,40,18,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7004 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7005 : PairBound 9 := { available := 65, camps := [], pairs := [(2,1),(4,1)], upper := (rows 35 134 44 26 81 288 68 193 321), lower := (rows 35 134 44 26 81 288 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 313 78 145 273), good := (rows 497 196 108 508 497 288 68 128 288) }] }

theorem u7005 : Upper (D 6) (R 6) [34,132,40,18,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7005 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7006 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(2,1)], upper := (rows 35 134 44 26 84 288 65 193 321), lower := (rows 35 134 44 26 84 288 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 369 65 193 321), good := (rows 481 132 44 60 500 288 481 128 288) }] }

theorem u7006 : Upper (D 6) (R 6) [34,132,40,18,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7006 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7007 : Route 9 := (fun mask => (mask,id))

def c7007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7007 : Upper (D 6) (R 6) [34,132,40,18,257,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,257,64,1] 13 (by decide) (choices 1) [4,64] r7007 c7007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u525
  · exact u526

def b7008 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 134 44 26 273 96 68 193 321), lower := (rows 35 134 44 26 273 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 111 78 129 257), good := (rows 497 228 108 124 433 96 100 128 256) }] }

theorem u7008 : Upper (D 6) (R 6) [34,132,40,18,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7008 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7009 : Route 9 := (fun mask => (mask,id))

def c7009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7009 : Upper (D 6) (R 6) [34,132,40,18,260,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,260,64,1] 13 (by decide) (choices 1) [1,64] r7009 c7009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u527
  · exact u528

def b7010 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 73 82 288 65 148 276), lower := (rows 35 134 44 73 82 288 65 128 256), losses := [] }

theorem u7010 : Upper (D 6) (R 6) [34,132,40,65,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7010 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7011 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 44 73 82 288 68 145 273), lower := (rows 35 134 44 73 82 288 68 128 256), losses := [] }

theorem u7011 : Upper (D 6) (R 6) [34,132,40,65,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7011 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7012 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2)], upper := (rows 35 134 44 73 82 288 80 133 261), lower := (rows 35 134 44 73 82 288 80 128 256), losses := [] }

theorem u7012 : Upper (D 6) (R 6) [34,132,40,65,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7012 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7013 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 74 81 288 65 148 276), lower := (rows 35 134 44 74 81 288 65 128 256), losses := [] }

theorem u7013 : Upper (D 6) (R 6) [34,132,40,66,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7013 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7014 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 134 44 74 81 288 68 145 273), lower := (rows 35 134 44 74 81 288 68 128 256), losses := [] }

theorem u7014 : Upper (D 6) (R 6) [34,132,40,66,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7014 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7015 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 4 }], pairs := [(3,2)], upper := (rows 35 134 44 74 81 288 80 133 261), lower := (rows 35 134 44 74 81 288 80 128 256), losses := [] }

theorem u7015 : Upper (D 6) (R 6) [34,132,40,66,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7015 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7016 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 74 273 48 65 196 324), lower := (rows 35 134 44 74 273 48 65 128 256), losses := [] }

theorem u7016 : Upper (D 6) (R 6) [34,132,40,66,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7016 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7017 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 134 44 74 273 48 68 193 321), lower := (rows 35 134 44 74 273 48 68 128 256), losses := [] }

theorem u7017 : Upper (D 6) (R 6) [34,132,40,66,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7017 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7018 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 44 88 276 33 65 194 322), lower := (rows 35 134 44 88 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 97 97 128 256), good := (rows 97 132 108 124 276 97 97 128 256) }] }

theorem u7018 : Upper (D 6) (R 6) [34,132,40,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7018 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7019 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,5)], upper := (rows 35 134 44 88 276 33 66 193 321), lower := (rows 35 134 44 88 276 33 66 128 256), losses := [{ target := 5, region := (rows 1 6 4 30 20 0 87 161 289), good := (rows 459 222 478 88 350 449 74 128 256) }] }

theorem u7019 : Upper (D 6) (R 6) [34,132,40,80,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7019 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7019
end Delivery.IrregularNine14.P06
