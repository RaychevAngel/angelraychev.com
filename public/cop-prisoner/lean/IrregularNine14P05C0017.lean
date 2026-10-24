import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000
import IrregularNine14P05C0001

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 268 25 34 65 168 296), lower := (rows 7 82 164 268 25 34 65 128 256), losses := [] }

theorem u1020 : Upper (D 5) (R 5) [6,80,160,260,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1020
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 268 25 34 72 161 289), lower := (rows 7 82 164 268 25 34 72 128 256), losses := [] }

theorem u1021 : Upper (D 5) (R 5) [6,80,160,260,9,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1021
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 82 164 268 25 34 96 137 265), lower := (rows 7 82 164 268 25 34 96 128 256), losses := [] }

theorem u1022 : Upper (D 5) (R 5) [6,80,160,260,9,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1022
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 82 164 268 25 40 65 162 290), lower := (rows 7 82 164 268 25 40 65 128 256), losses := [] }

theorem u1023 : Upper (D 5) (R 5) [6,80,160,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1023
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 268 25 40 66 161 289), lower := (rows 7 82 164 268 25 40 66 128 256), losses := [] }

theorem u1024 : Upper (D 5) (R 5) [6,80,160,260,9,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1024
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 82 164 268 25 40 96 131 259), lower := (rows 7 82 164 268 25 40 96 128 256), losses := [] }

theorem u1025 : Upper (D 5) (R 5) [6,80,160,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1025
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 264, targets := 1 },{ cop := 0, region := 264, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 82 164 268 56 33 65 138 266), lower := (rows 7 82 164 268 56 33 65 128 256), losses := [] }

theorem u1026 : Upper (D 5) (R 5) [6,80,160,260,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1026
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 82 164 268 56 33 66 137 265), lower := (rows 7 82 164 268 56 33 66 128 256), losses := [] }

theorem u1027 : Upper (D 5) (R 5) [6,80,160,260,40,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1027
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1028 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 82 164 268 56 33 72 131 259), lower := (rows 7 82 164 268 56 33 72 128 256), losses := [] }

theorem u1028 : Upper (D 5) (R 5) [6,80,160,260,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1028
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1029 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 82 164 296 25 33 66 140 268), lower := (rows 7 82 164 296 25 33 66 128 256), losses := [] }

theorem u1029 : Upper (D 5) (R 5) [6,80,160,288,9,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1029
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 296 25 33 68 138 266), lower := (rows 7 82 164 296 25 33 68 128 256), losses := [] }

theorem u1030 : Upper (D 5) (R 5) [6,80,160,288,9,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1030
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 82 164 296 25 33 72 134 262), lower := (rows 7 82 164 296 25 33 72 128 256), losses := [] }

theorem u1031 : Upper (D 5) (R 5) [6,80,160,288,9,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1031
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 296 25 34 65 140 268), lower := (rows 7 82 164 296 25 34 65 128 256), losses := [] }

theorem u1032 : Upper (D 5) (R 5) [6,80,160,288,9,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1032
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 164 296 25 34 68 137 265), lower := (rows 7 82 164 296 25 34 68 128 256), losses := [] }

theorem u1033 : Upper (D 5) (R 5) [6,80,160,288,9,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1033
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 82 164 296 25 34 72 133 261), lower := (rows 7 82 164 296 25 34 72 128 256), losses := [] }

theorem u1034 : Upper (D 5) (R 5) [6,80,160,288,9,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1034
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1035 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 388, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 388 42 28 33 65 168 296), lower := (rows 7 82 388 42 28 33 65 128 256), losses := [] }

theorem u1035 : Upper (D 5) (R 5) [6,80,384,34,12,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1035
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1036 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 420, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 7 82 388 42 28 33 72 161 289), lower := (rows 7 82 388 42 28 33 72 128 256), losses := [] }

theorem u1036 : Upper (D 5) (R 5) [6,80,384,34,12,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1036
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 82 388 42 28 33 96 137 265), lower := (rows 7 82 388 42 28 33 96 128 256), losses := [] }

theorem u1037 : Upper (D 5) (R 5) [6,80,384,34,12,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1037
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 73 148 288 66 140 268), lower := (rows 19 35 44 73 148 288 66 128 256), losses := [] }

theorem u1038 : Upper (D 5) (R 5) [18,33,40,65,132,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1038
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 76, targets := 2 }], pairs := [(2,1)], upper := (rows 19 35 44 73 148 288 68 138 266), lower := (rows 19 35 44 73 148 288 68 128 256), losses := [] }

theorem u1039 : Upper (D 5) (R 5) [18,33,40,65,132,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1039
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 72, targets := 2 }], pairs := [(3,1)], upper := (rows 19 35 44 73 148 288 72 134 262), lower := (rows 19 35 44 73 148 288 72 128 256), losses := [] }

theorem u1040 : Upper (D 5) (R 5) [18,33,40,65,132,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1040
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1041 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 74 148 288 65 140 268), lower := (rows 19 35 44 74 148 288 65 128 256), losses := [] }

theorem u1041 : Upper (D 5) (R 5) [18,33,40,66,132,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1041
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1042 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 74 148 288 68 137 265), lower := (rows 19 35 44 74 148 288 68 128 256), losses := [] }

theorem u1042 : Upper (D 5) (R 5) [18,33,40,66,132,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1042
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 147, targets := 8 }], pairs := [(0,3)], upper := (rows 19 35 44 74 148 288 72 133 261), lower := (rows 19 35 44 74 148 288 72 128 256), losses := [] }

theorem u1043 : Upper (D 5) (R 5) [18,33,40,66,132,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1043
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 292, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 74 152 288 65 132 260), lower := (rows 19 35 44 74 152 288 65 128 256), losses := [] }

theorem u1044 : Upper (D 5) (R 5) [18,33,40,66,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1044
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 74 152 288 68 133 261), lower := (rows 19 35 44 74 152 288 68 128 256), losses := [] }

theorem u1045 : Upper (D 5) (R 5) [18,33,40,66,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1045
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 76, targets := 2 }], pairs := [(2,1)], upper := (rows 19 35 44 76 148 288 65 138 266), lower := (rows 19 35 44 76 148 288 65 128 256), losses := [] }

theorem u1046 : Upper (D 5) (R 5) [18,33,40,68,132,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1046
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 76 148 288 66 137 265), lower := (rows 19 35 44 76 148 288 66 128 256), losses := [] }

theorem u1047 : Upper (D 5) (R 5) [18,33,40,68,132,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1047
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 291, targets := 4 }], pairs := [(0,2)], upper := (rows 19 35 44 76 148 288 72 131 259), lower := (rows 19 35 44 76 148 288 72 128 256), losses := [] }

theorem u1048 : Upper (D 5) (R 5) [18,33,40,68,132,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1048
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 76, targets := 2 }], pairs := [(2,1)], upper := (rows 19 35 44 76 152 288 65 134 262), lower := (rows 19 35 44 76 152 288 65 128 256), losses := [] }

theorem u1049 : Upper (D 5) (R 5) [18,33,40,68,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1049
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 44 76 152 288 66 133 261), lower := (rows 19 35 44 76 152 288 66 128 256), losses := [] }

theorem u1050 : Upper (D 5) (R 5) [18,33,40,68,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1050
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1051 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 291, targets := 4 }], pairs := [(0,2)], upper := (rows 19 35 44 76 152 288 68 131 259), lower := (rows 19 35 44 76 152 288 68 128 256), losses := [] }

theorem u1051 : Upper (D 5) (R 5) [18,33,40,68,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1051
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1052 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 69 138 276 40 68 168 296), lower := (rows 19 35 69 138 276 40 68 128 256), losses := [] }

theorem u1052 : Upper (D 5) (R 5) [18,33,65,130,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1052
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 36, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 35 69 138 276 40 72 164 292), lower := (rows 19 35 69 138 276 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 111 111 148 276), good := (rows 506 106 508 234 500 104 104 128 256) }] }

theorem u1053 : Upper (D 5) (R 5) [18,33,65,130,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1053
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 68, targets := 2 },{ cop := 1, region := 68, targets := 8 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 69 138 276 40 96 140 268), lower := (rows 19 35 69 138 276 40 96 128 256), losses := [] }

theorem u1054 : Upper (D 5) (R 5) [18,33,65,130,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1054
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 411, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 69 138 280 36 68 168 296), lower := (rows 19 35 69 138 280 36 68 128 256), losses := [] }

theorem u1055 : Upper (D 5) (R 5) [18,33,65,130,264,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1055
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 34, targets := 8 }], pairs := [(1,3),(3,0)], upper := (rows 19 35 69 138 280 36 72 164 292), lower := (rows 19 35 69 138 280 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 91 164 292), good := (rows 90 506 484 218 344 420 72 128 256) }] }

theorem u1056 : Upper (D 5) (R 5) [18,33,65,130,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1056
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 69 138 280 36 96 140 268), lower := (rows 19 35 69 138 280 36 96 128 256), losses := [] }

theorem u1057 : Upper (D 5) (R 5) [18,33,65,130,264,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1057
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 69 140 276 40 66 168 296), lower := (rows 19 35 69 140 276 40 66 128 256), losses := [] }

theorem u1058 : Upper (D 5) (R 5) [18,33,65,132,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1058
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 34, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 35 69 140 276 40 72 162 290), lower := (rows 19 35 69 140 276 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 124 124 131 259), good := (rows 498 482 508 252 380 104 104 128 256) }] }

theorem u1059 : Upper (D 5) (R 5) [18,33,65,132,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1059
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 68, targets := 2 },{ cop := 1, region := 68, targets := 8 }], pairs := [(2,1),(2,3)], upper := (rows 19 35 69 140 276 40 96 138 266), lower := (rows 19 35 69 140 276 40 96 128 256), losses := [] }

theorem u1060 : Upper (D 5) (R 5) [18,33,65,132,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1060
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 424, targets := 1 }], pairs := [(3,0)], upper := (rows 19 35 69 168 28 288 66 140 268), lower := (rows 19 35 69 168 28 288 66 128 256), losses := [] }

theorem u1061 : Upper (D 5) (R 5) [18,33,65,160,12,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1061
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 19 35 69 168 28 288 68 138 266), lower := (rows 19 35 69 168 28 288 68 128 256), losses := [] }

theorem u1062 : Upper (D 5) (R 5) [18,33,65,160,12,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1062
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 19 35 69 168 28 288 72 134 262), lower := (rows 19 35 69 168 28 288 72 128 256), losses := [] }

theorem u1063 : Upper (D 5) (R 5) [18,33,65,160,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1063
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 69 168 280 36 66 140 268), lower := (rows 19 35 69 168 280 36 66 128 256), losses := [] }

theorem u1064 : Upper (D 5) (R 5) [18,33,65,160,264,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1064
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 411, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 69 168 280 36 68 138 266), lower := (rows 19 35 69 168 280 36 68 128 256), losses := [] }

theorem u1065 : Upper (D 5) (R 5) [18,33,65,160,264,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1065
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 34, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 35 69 168 280 36 72 134 262), lower := (rows 19 35 69 168 280 36 72 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 39 88 128 256), good := (rows 117 37 101 232 344 36 72 128 256) }] }

theorem u1066 : Upper (D 5) (R 5) [18,33,65,160,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1066
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 70 140 276 40 65 168 296), lower := (rows 19 35 70 140 276 40 65 128 256), losses := [] }

theorem u1067 : Upper (D 5) (R 5) [18,33,66,132,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1067
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0),(3,1)], upper := (rows 19 35 70 140 276 40 72 161 289), lower := (rows 19 35 70 140 276 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 104 104 128 256), good := (rows 22 102 102 236 276 104 104 128 256) },{ target := 1, region := (rows 1 0 4 12 20 124 124 131 259), good := (rows 497 481 508 252 380 104 104 128 256) }] }

theorem u1068 : Upper (D 5) (R 5) [18,33,66,132,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1068
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 35 70 140 276 40 96 137 265), lower := (rows 19 35 70 140 276 40 96 128 256), losses := [] }

theorem u1069 : Upper (D 5) (R 5) [18,33,66,132,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1069
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 424, targets := 1 }], pairs := [(3,0)], upper := (rows 19 35 70 168 28 288 65 140 268), lower := (rows 19 35 70 168 28 288 65 128 256), losses := [] }

theorem u1070 : Upper (D 5) (R 5) [18,33,66,160,12,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1070
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 19 35 70 168 28 288 68 137 265), lower := (rows 19 35 70 168 28 288 68 128 256), losses := [] }

theorem u1071 : Upper (D 5) (R 5) [18,33,66,160,12,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1071
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 19 35 70 168 28 288 72 133 261), lower := (rows 19 35 70 168 28 288 72 128 256), losses := [] }

theorem u1072 : Upper (D 5) (R 5) [18,33,66,160,12,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1072
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 168, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 70 168 280 36 65 140 268), lower := (rows 19 35 70 168 280 36 65 128 256), losses := [] }

theorem u1073 : Upper (D 5) (R 5) [18,33,66,160,264,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1073
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 411, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 70 168 280 36 68 137 265), lower := (rows 19 35 70 168 280 36 68 128 256), losses := [] }

theorem u1074 : Upper (D 5) (R 5) [18,33,66,160,264,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1074
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1075 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0),(2,5)], upper := (rows 19 35 70 168 280 36 72 133 261), lower := (rows 19 35 70 168 280 36 72 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 39 88 128 256), good := (rows 118 38 102 232 344 36 72 128 256) },{ target := 5, region := (rows 1 2 5 8 16 0 88 131 259), good := (rows 471 391 454 200 344 4 72 128 256) }] }

theorem u1075 : Upper (D 5) (R 5) [18,33,66,160,264,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1075
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1076 : Route 9 := (fun mask => (mask,id))

def c1076 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1076 : Upper (D 5) (R 5) [18,33,72,160,264,4,1] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160,264,4,1] 13 (by decide) (choices 1) [2,4] r1076 c1076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u58
  · exact u59

def r1077 : Route 9 := (fun mask => (mask,id))

def c1077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1077 : Upper (D 5) (R 5) [18,33,72,160,264,4,2] 13 := by
  apply FastRouting.sound _ _ [18,33,72,160,264,4,2] 13 (by decide) (choices 1) [1,4] r1077 c1077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u60
  · exact u61

def b1078 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 411, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 76 168 280 36 68 131 259), lower := (rows 19 35 76 168 280 36 68 128 256), losses := [] }

theorem u1078 : Upper (D 5) (R 5) [18,33,72,160,264,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1078
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 8 }], pairs := [(2,3)], upper := (rows 19 38 69 41 152 288 66 140 268), lower := (rows 19 38 69 41 152 288 66 128 256), losses := [] }

theorem u1079 : Upper (D 5) (R 5) [18,36,65,33,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1079
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P05
