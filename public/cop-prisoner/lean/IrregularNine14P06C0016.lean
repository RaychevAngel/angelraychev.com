import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b960 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 26 133 104 276 33 96 194 322), lower := (rows 7 26 133 104 276 33 96 128 256), losses := [] }

theorem u960 : Upper (D 6) (R 6) [6,24,129,96,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b960
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 26 133 104 276 34 96 193 321), lower := (rows 7 26 133 104 276 34 96 128 256), losses := [] }

theorem u961 : Upper (D 6) (R 6) [6,24,129,96,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b961
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 274, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 104 304 36 65 194 322), lower := (rows 7 26 133 104 304 36 65 128 256), losses := [] }

theorem u962 : Upper (D 6) (R 6) [6,24,129,96,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b962
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 133 104 304 36 66 193 321), lower := (rows 7 26 133 104 304 36 66 128 256), losses := [] }

theorem u963 : Upper (D 6) (R 6) [6,24,129,96,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b963
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 73 273 96 66 164 292), lower := (rows 7 26 164 73 273 96 66 128 256), losses := [] }

theorem u964 : Upper (D 6) (R 6) [6,24,160,65,257,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b964
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 306, targets := 4 },{ cop := 7, region := 100, targets := 1 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 26 164 73 273 96 68 162 290), lower := (rows 7 26 164 73 273 96 68 128 256), losses := [] }

theorem u965 : Upper (D 6) (R 6) [6,24,160,65,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b965
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 0, region := 272, targets := 32 }], pairs := [(3,1),(3,2),(4,5)], upper := (rows 7 26 164 73 273 96 96 134 262), lower := (rows 7 26 164 73 273 96 96 128 256), losses := [] }

theorem u966 : Upper (D 6) (R 6) [6,24,160,65,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b966
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 73 274 96 65 164 292), lower := (rows 7 26 164 73 274 96 65 128 256), losses := [] }

theorem u967 : Upper (D 6) (R 6) [6,24,160,65,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b967
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 306, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 7 26 164 73 274 96 68 161 289), lower := (rows 7 26 164 73 274 96 68 128 256), losses := [] }

theorem u968 : Upper (D 6) (R 6) [6,24,160,65,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b968
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 272, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 164 73 274 96 96 133 261), lower := (rows 7 26 164 73 274 96 96 128 256), losses := [] }

theorem u969 : Upper (D 6) (R 6) [6,24,160,65,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b969
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 164 73 276 33 66 224 352), lower := (rows 7 26 164 73 276 33 66 128 256), losses := [] }

theorem u970 : Upper (D 6) (R 6) [6,24,160,65,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b970
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 72, targets := 6 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 7 26 164 73 276 33 96 194 322), lower := (rows 7 26 164 73 276 33 96 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 49 32 100 137 265), good := (rows 470 410 244 474 340 500 116 128 256) }] }

theorem u971 : Upper (D 6) (R 6) [6,24,160,65,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b971
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 73 276 34 65 224 352), lower := (rows 7 26 164 73 276 34 65 128 256), losses := [] }

theorem u972 : Upper (D 6) (R 6) [6,24,160,65,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b972
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 104, targets := 4 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 26 164 73 276 34 96 193 321), lower := (rows 7 26 164 73 276 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 32 100 137 265), good := (rows 477 408 228 473 340 96 96 128 256) }] }

theorem u973 : Upper (D 6) (R 6) [6,24,160,65,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 73 276 96 65 162 290), lower := (rows 7 26 164 73 276 96 65 128 256), losses := [] }

theorem u974 : Upper (D 6) (R 6) [6,24,160,65,260,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b974
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 164 73 276 96 66 161 289), lower := (rows 7 26 164 73 276 96 66 128 256), losses := [] }

theorem u975 : Upper (D 6) (R 6) [6,24,160,65,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b975
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 272, targets := 96 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(4,5),(4,6)], upper := (rows 7 26 164 73 276 96 96 131 259), lower := (rows 7 26 164 73 276 96 96 128 256), losses := [] }

theorem u976 : Upper (D 6) (R 6) [6,24,160,65,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b976
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 73 304 34 65 196 324), lower := (rows 7 26 164 73 304 34 65 128 256), losses := [] }

theorem u977 : Upper (D 6) (R 6) [6,24,160,65,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b977
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 3, region := 306, targets := 4 }], pairs := [(1,2),(3,1),(3,5)], upper := (rows 7 26 164 73 304 34 68 193 321), lower := (rows 7 26 164 73 304 34 68 128 256), losses := [] }

theorem u978 : Upper (D 6) (R 6) [6,24,160,65,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b978
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 73 304 96 65 134 262), lower := (rows 7 26 164 73 304 96 65 128 256), losses := [] }

theorem u979 : Upper (D 6) (R 6) [6,24,160,65,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b979
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 436, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 164 73 304 96 66 133 261), lower := (rows 7 26 164 73 304 96 66 128 256), losses := [] }

theorem u980 : Upper (D 6) (R 6) [6,24,160,65,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 306, targets := 4 },{ cop := 7, region := 100, targets := 1 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 26 164 73 304 96 68 131 259), lower := (rows 7 26 164 73 304 96 68 128 256), losses := [] }

theorem u981 : Upper (D 6) (R 6) [6,24,160,65,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b981
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 73 336 33 66 164 292), lower := (rows 7 26 164 73 336 33 66 128 256), losses := [] }

theorem u982 : Upper (D 6) (R 6) [6,24,160,65,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b982
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 306, targets := 4 }], pairs := [(0,6),(1,2),(2,6)], upper := (rows 7 26 164 73 336 33 68 162 290), lower := (rows 7 26 164 73 336 33 68 128 256), losses := [] }

theorem u983 : Upper (D 6) (R 6) [6,24,160,65,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b983
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(3,1),(3,2)], upper := (rows 7 26 164 73 336 33 96 134 262), lower := (rows 7 26 164 73 336 33 96 128 256), losses := [] }

theorem u984 : Upper (D 6) (R 6) [6,24,160,65,320,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b984
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 73 336 34 65 164 292), lower := (rows 7 26 164 73 336 34 65 128 256), losses := [] }

theorem u985 : Upper (D 6) (R 6) [6,24,160,65,320,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b985
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(3,1),(3,5)], upper := (rows 7 26 164 73 336 34 68 161 289), lower := (rows 7 26 164 73 336 34 68 128 256), losses := [] }

theorem u986 : Upper (D 6) (R 6) [6,24,160,65,320,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b986
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 104, targets := 4 }], pairs := [(0,6),(2,6),(3,2)], upper := (rows 7 26 164 73 336 34 96 133 261), lower := (rows 7 26 164 73 336 34 96 128 256), losses := [] }

theorem u987 : Upper (D 6) (R 6) [6,24,160,65,320,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b987
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 26 164 74 273 96 65 164 292), lower := (rows 7 26 164 74 273 96 65 128 256), losses := [] }

theorem u988 : Upper (D 6) (R 6) [6,24,160,66,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b988
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 164 74 273 96 68 161 289), lower := (rows 7 26 164 74 273 96 68 128 256), losses := [] }

theorem u989 : Upper (D 6) (R 6) [6,24,160,66,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b989
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 106, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 164 74 273 96 96 133 261), lower := (rows 7 26 164 74 273 96 96 128 256), losses := [] }

theorem u990 : Upper (D 6) (R 6) [6,24,160,66,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b990
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,2)], upper := (rows 7 26 164 76 273 33 66 224 352), lower := (rows 7 26 164 76 273 33 66 128 256), losses := [] }

theorem u991 : Upper (D 6) (R 6) [6,24,160,68,257,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b991
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 26 164 76 273 33 96 194 322), lower := (rows 7 26 164 76 273 33 96 128 256), losses := [] }

theorem u992 : Upper (D 6) (R 6) [6,24,160,68,257,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b992
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 26 164 76 273 34 65 224 352), lower := (rows 7 26 164 76 273 34 65 128 256), losses := [] }

theorem u993 : Upper (D 6) (R 6) [6,24,160,68,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b993
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 26 164 76 273 34 96 193 321), lower := (rows 7 26 164 76 273 34 96 128 256), losses := [] }

theorem u994 : Upper (D 6) (R 6) [6,24,160,68,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b994
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 2 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 26 164 76 273 96 65 162 290), lower := (rows 7 26 164 76 273 96 65 128 256), losses := [] }

theorem u995 : Upper (D 6) (R 6) [6,24,160,68,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b995
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b996 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,2)], upper := (rows 7 26 164 76 273 96 66 161 289), lower := (rows 7 26 164 76 273 96 66 128 256), losses := [] }

theorem u996 : Upper (D 6) (R 6) [6,24,160,68,257,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b996
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 275, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 164 76 273 96 96 131 259), lower := (rows 7 26 164 76 273 96 96 128 256), losses := [] }

theorem u997 : Upper (D 6) (R 6) [6,24,160,68,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b997
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 72, targets := 2 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 26 164 76 304 33 65 194 322), lower := (rows 7 26 164 76 304 33 65 128 256), losses := [] }

theorem u998 : Upper (D 6) (R 6) [6,24,160,68,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b998
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,2)], upper := (rows 7 26 164 76 304 33 66 193 321), lower := (rows 7 26 164 76 304 33 66 128 256), losses := [] }

theorem u999 : Upper (D 6) (R 6) [6,24,160,68,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b999
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 72, targets := 2 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 26 164 76 304 96 65 131 259), lower := (rows 7 26 164 76 304 96 65 128 256), losses := [] }

theorem u1000 : Upper (D 6) (R 6) [6,24,160,68,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1000
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,2)], upper := (rows 7 26 164 76 304 96 66 129 257), lower := (rows 7 26 164 76 304 96 66 128 256), losses := [] }

theorem u1001 : Upper (D 6) (R 6) [6,24,160,68,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1001
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 26 164 104 273 34 65 196 324), lower := (rows 7 26 164 104 273 34 65 128 256), losses := [] }

theorem u1002 : Upper (D 6) (R 6) [6,24,160,96,257,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1002
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 2, region := 72, targets := 1 }], pairs := [(3,0),(4,1),(4,5)], upper := (rows 7 26 164 104 273 34 68 193 321), lower := (rows 7 26 164 104 273 34 68 128 256), losses := [] }

theorem u1003 : Upper (D 6) (R 6) [6,24,160,96,257,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1003
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 26 164 104 276 33 65 194 322), lower := (rows 7 26 164 104 276 33 65 128 256), losses := [] }

theorem u1004 : Upper (D 6) (R 6) [6,24,160,96,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1004
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1005 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 104, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,0),(3,2),(4,5)], upper := (rows 7 26 164 104 276 33 66 193 321), lower := (rows 7 26 164 104 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 128 256), good := (rows 70 90 172 104 276 104 66 128 256) }] }

theorem u1005 : Upper (D 6) (R 6) [6,24,160,96,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1005
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1006 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 104, targets := 4 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 7 26 388 41 84 96 65 162 290), lower := (rows 7 26 388 41 84 96 65 128 256), losses := [] }

theorem u1006 : Upper (D 6) (R 6) [6,24,384,33,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1006
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1007 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 388, targets := 66 },{ cop := 0, region := 80, targets := 1 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 7 26 388 41 84 96 66 161 289), lower := (rows 7 26 388 41 84 96 66 128 256), losses := [] }

theorem u1007 : Upper (D 6) (R 6) [6,24,384,33,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1007
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 26 388 41 84 96 96 131 259), lower := (rows 7 26 388 41 84 96 96 128 256), losses := [] }

theorem u1008 : Upper (D 6) (R 6) [6,24,384,33,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1008
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 432, targets := 3 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(4,0),(4,1)], upper := (rows 7 35 76 26 400 96 65 164 292), lower := (rows 7 35 76 26 400 96 65 128 256), losses := [] }

theorem u1009 : Upper (D 6) (R 6) [6,33,72,18,384,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1009
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 76 26 400 96 68 161 289), lower := (rows 7 35 76 26 400 96 68 128 256), losses := [] }

theorem u1010 : Upper (D 6) (R 6) [6,33,72,18,384,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1010
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 76 26 400 96 96 133 261), lower := (rows 7 35 76 26 400 96 96 128 256), losses := [] }

theorem u1011 : Upper (D 6) (R 6) [6,33,72,18,384,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1011
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 138 112 288 65 148 276), lower := (rows 7 35 76 138 112 288 65 128 256), losses := [] }

theorem u1012 : Upper (D 6) (R 6) [6,33,72,130,96,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1012
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 138 112 288 68 145 273), lower := (rows 7 35 76 138 112 288 68 128 256), losses := [] }

theorem u1013 : Upper (D 6) (R 6) [6,33,72,130,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1013
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 138 112 288 80 133 261), lower := (rows 7 35 76 138 112 288 80 128 256), losses := [] }

theorem u1014 : Upper (D 6) (R 6) [6,33,72,130,96,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1014
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 304, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 138 336 48 65 164 292), lower := (rows 7 35 76 138 336 48 65 128 256), losses := [] }

theorem u1015 : Upper (D 6) (R 6) [6,33,72,130,320,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1015
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 136, targets := 68 }], pairs := [(3,2),(3,6)], upper := (rows 7 35 76 138 336 48 68 161 289), lower := (rows 7 35 76 138 336 48 68 128 256), losses := [] }

theorem u1016 : Upper (D 6) (R 6) [6,33,72,130,320,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1016
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 138 336 48 96 133 261), lower := (rows 7 35 76 138 336 48 96 128 256), losses := [] }

theorem u1017 : Upper (D 6) (R 6) [6,33,72,130,320,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1017
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 7 35 76 152 274 96 65 164 292), lower := (rows 7 35 76 152 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 91 19 100 64 231 359), good := (rows 446 446 492 152 410 492 508 128 256) }] }

theorem u1018 : Upper (D 6) (R 6) [6,33,72,144,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1018
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 408, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 76 152 274 96 68 161 289), lower := (rows 7 35 76 152 274 96 68 128 256), losses := [] }

theorem u1019 : Upper (D 6) (R 6) [6,33,72,144,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1019
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P06
