import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 19 38 69 41 152 288 68 138 266), lower := (rows 19 38 69 41 152 288 68 128 256), losses := [] }

theorem u1080 : Upper (D 5) (R 5) [18,36,65,33,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 69 41 152 288 72 134 262), lower := (rows 19 38 69 41 152 288 72 128 256), losses := [] }

theorem u1081 : Upper (D 5) (R 5) [18,36,65,33,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 40 }], pairs := [(2,3),(2,5)], upper := (rows 19 38 69 137 276 40 66 168 296), lower := (rows 19 38 69 137 276 40 66 128 256), losses := [] }

theorem u1082 : Upper (D 5) (R 5) [18,36,65,129,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 38 69 137 276 40 72 162 290), lower := (rows 19 38 69 137 276 40 72 128 256), losses := [] }

theorem u1083 : Upper (D 5) (R 5) [18,36,65,129,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 69 137 276 40 96 138 266), lower := (rows 19 38 69 137 276 40 96 128 256), losses := [] }

theorem u1084 : Upper (D 5) (R 5) [18,36,65,129,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1084
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 40 }], pairs := [(2,3),(2,5)], upper := (rows 19 38 69 137 280 40 66 164 292), lower := (rows 19 38 69 137 280 40 66 128 256), losses := [] }

theorem u1085 : Upper (D 5) (R 5) [18,36,65,129,264,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1085
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 68, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 38 69 137 280 40 68 162 290), lower := (rows 19 38 69 137 280 40 68 128 256), losses := [] }

theorem u1086 : Upper (D 5) (R 5) [18,36,65,129,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 69 137 280 40 96 134 262), lower := (rows 19 38 69 137 280 40 96 128 256), losses := [] }

theorem u1087 : Upper (D 5) (R 5) [18,36,65,129,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1087
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 38 69 138 276 40 65 168 296), lower := (rows 19 38 69 138 276 40 65 128 256), losses := [] }

theorem u1088 : Upper (D 5) (R 5) [18,36,65,130,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 38 69 138 276 40 72 161 289), lower := (rows 19 38 69 138 276 40 72 128 256), losses := [] }

theorem u1089 : Upper (D 5) (R 5) [18,36,65,130,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 69 138 276 40 96 137 265), lower := (rows 19 38 69 138 276 40 96 128 256), losses := [] }

theorem u1090 : Upper (D 5) (R 5) [18,36,65,130,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 38 69 138 280 40 65 164 292), lower := (rows 19 38 69 138 280 40 65 128 256), losses := [] }

theorem u1091 : Upper (D 5) (R 5) [18,36,65,130,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1091
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 38 69 138 280 40 68 161 289), lower := (rows 19 38 69 138 280 40 68 128 256), losses := [] }

theorem u1092 : Upper (D 5) (R 5) [18,36,65,130,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1092
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 69 138 280 40 96 133 261), lower := (rows 19 38 69 138 280 40 96 128 256), losses := [] }

theorem u1093 : Upper (D 5) (R 5) [18,36,65,130,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1093
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 68, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 38 69 140 280 40 65 162 290), lower := (rows 19 38 69 140 280 40 65 128 256), losses := [] }

theorem u1094 : Upper (D 5) (R 5) [18,36,65,132,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 40 }], pairs := [(2,3),(2,5)], upper := (rows 19 38 69 140 280 40 66 161 289), lower := (rows 19 38 69 140 280 40 66 128 256), losses := [] }

theorem u1095 : Upper (D 5) (R 5) [18,36,65,132,264,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 69 140 280 40 96 131 259), lower := (rows 19 38 69 140 280 40 96 128 256), losses := [] }

theorem u1096 : Upper (D 5) (R 5) [18,36,65,132,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1096
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 8 }], pairs := [(2,3)], upper := (rows 19 38 70 41 152 288 65 140 268), lower := (rows 19 38 70 41 152 288 65 128 256), losses := [] }

theorem u1097 : Upper (D 5) (R 5) [18,36,66,33,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1097
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 19 38 70 41 152 288 68 137 265), lower := (rows 19 38 70 41 152 288 68 128 256), losses := [] }

theorem u1098 : Upper (D 5) (R 5) [18,36,66,33,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 70 41 152 288 72 133 261), lower := (rows 19 38 70 41 152 288 72 128 256), losses := [] }

theorem u1099 : Upper (D 5) (R 5) [18,36,66,33,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1099
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 137 280 33 68 168 296), lower := (rows 19 38 70 137 280 33 68 128 256), losses := [] }

theorem u1100 : Upper (D 5) (R 5) [18,36,66,129,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1100
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 36, camps := [], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 137 280 33 72 164 292), lower := (rows 19 38 70 137 280 33 72 128 256), losses := [{ target := 0, region := (rows 0 34 5 8 16 32 88 162 290), good := (rows 470 422 454 204 344 422 72 128 256) }] }

theorem u1101 : Upper (D 5) (R 5) [18,36,66,129,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 137 280 33 96 140 268), lower := (rows 19 38 70 137 280 33 96 128 256), losses := [] }

theorem u1102 : Upper (D 5) (R 5) [18,36,66,129,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 68, targets := 40 }], pairs := [(2,3),(2,5)], upper := (rows 19 38 70 137 280 40 65 164 292), lower := (rows 19 38 70 137 280 40 65 128 256), losses := [] }

theorem u1103 : Upper (D 5) (R 5) [18,36,66,129,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1103
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 137 280 40 68 161 289), lower := (rows 19 38 70 137 280 40 68 128 256), losses := [] }

theorem u1104 : Upper (D 5) (R 5) [18,36,66,129,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1105 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 137 280 40 96 133 261), lower := (rows 19 38 70 137 280 40 96 128 256), losses := [] }

theorem u1105 : Upper (D 5) (R 5) [18,36,66,129,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 288, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 140 25 40 65 416 288), lower := (rows 19 38 70 140 25 40 65 128 256), losses := [] }

theorem u1106 : Upper (D 5) (R 5) [18,36,66,132,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1106
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 140 25 40 96 385 257), lower := (rows 19 38 70 140 25 40 96 128 256), losses := [] }

theorem u1107 : Upper (D 5) (R 5) [18,36,66,132,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 70 140 25 40 320 161 289), lower := (rows 19 38 70 140 25 40 320 128 256), losses := [] }

theorem u1108 : Upper (D 5) (R 5) [18,36,66,132,9,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 70 140 25 288 65 168 296), lower := (rows 19 38 70 140 25 288 65 128 256), losses := [] }

theorem u1109 : Upper (D 5) (R 5) [18,36,66,132,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0)], upper := (rows 19 38 70 140 25 288 72 161 289), lower := (rows 19 38 70 140 25 288 72 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 288 88 128 256), good := (rows 86 38 70 204 92 288 72 128 288) }] }

theorem u1110 : Upper (D 5) (R 5) [18,36,66,132,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 70 140 25 288 96 137 265), lower := (rows 19 38 70 140 25 288 96 128 256), losses := [] }

theorem u1111 : Upper (D 5) (R 5) [18,36,66,132,9,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 174, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 140 273 40 65 168 296), lower := (rows 19 38 70 140 273 40 65 128 256), losses := [] }

theorem u1112 : Upper (D 5) (R 5) [18,36,66,132,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1112
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 273, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 38 70 140 273 40 72 161 289), lower := (rows 19 38 70 140 273 40 72 128 256), losses := [] }

theorem u1113 : Upper (D 5) (R 5) [18,36,66,132,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 140 273 40 96 137 265), lower := (rows 19 38 70 140 273 40 96 128 256), losses := [] }

theorem u1114 : Upper (D 5) (R 5) [18,36,66,132,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1114
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 70 140 280 33 65 168 296), lower := (rows 19 38 70 140 280 33 65 128 256), losses := [] }

theorem u1115 : Upper (D 5) (R 5) [18,36,66,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 33, camps := [], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 140 280 33 72 161 289), lower := (rows 19 38 70 140 280 33 72 128 256), losses := [{ target := 0, region := (rows 0 34 5 8 16 32 88 128 256), good := (rows 86 38 70 204 344 38 72 128 256) }] }

theorem u1116 : Upper (D 5) (R 5) [18,36,66,132,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 140 280 33 96 137 265), lower := (rows 19 38 70 140 280 33 96 128 256), losses := [] }

theorem u1117 : Upper (D 5) (R 5) [18,36,66,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1117
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 68, targets := 40 }], pairs := [(2,3),(2,5)], upper := (rows 19 38 70 140 280 40 65 161 289), lower := (rows 19 38 70 140 280 40 65 128 256), losses := [] }

theorem u1118 : Upper (D 5) (R 5) [18,36,66,132,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1118
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 140 280 40 96 129 257), lower := (rows 19 38 70 140 280 40 96 128 256), losses := [] }

theorem u1119 : Upper (D 5) (R 5) [18,36,66,132,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1119
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 103, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 38 70 168 280 33 65 140 268), lower := (rows 19 38 70 168 280 33 65 128 256), losses := [] }

theorem u1120 : Upper (D 5) (R 5) [18,36,66,160,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1120
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 168 280 33 68 137 265), lower := (rows 19 38 70 168 280 33 68 128 256), losses := [] }

theorem u1121 : Upper (D 5) (R 5) [18,36,66,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 168 280 33 72 133 261), lower := (rows 19 38 70 168 280 33 72 128 256), losses := [] }

theorem u1122 : Upper (D 5) (R 5) [18,36,66,160,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 70 392 25 40 65 164 292), lower := (rows 19 38 70 392 25 40 65 128 256), losses := [] }

theorem u1123 : Upper (D 5) (R 5) [18,36,66,384,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1123
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 38 70 392 25 40 68 161 289), lower := (rows 19 38 70 392 25 40 68 128 256), losses := [] }

theorem u1124 : Upper (D 5) (R 5) [18,36,66,384,9,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1124
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 38 70 392 25 40 96 133 261), lower := (rows 19 38 70 392 25 40 96 128 256), losses := [] }

theorem u1125 : Upper (D 5) (R 5) [18,36,66,384,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1125
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 76 41 152 288 65 134 262), lower := (rows 19 38 76 41 152 288 65 128 256), losses := [] }

theorem u1126 : Upper (D 5) (R 5) [18,36,72,33,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 76 41 152 288 66 133 261), lower := (rows 19 38 76 41 152 288 66 128 256), losses := [] }

theorem u1127 : Upper (D 5) (R 5) [18,36,72,33,136,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 153, targets := 4 }], pairs := [(0,2)], upper := (rows 19 38 76 41 152 288 68 131 259), lower := (rows 19 38 76 41 152 288 68 128 256), losses := [] }

theorem u1128 : Upper (D 5) (R 5) [18,36,72,33,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,1)], upper := (rows 19 38 76 137 280 33 66 164 292), lower := (rows 19 38 76 137 280 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 32 67 130 258), good := (rows 466 486 76 204 284 96 450 128 256) },{ target := 1, region := (rows 1 0 4 9 21 41 64 134 262), good := (rows 441 436 508 185 312 57 448 128 256) }] }

theorem u1129 : Upper (D 5) (R 5) [18,36,72,129,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 137 280 33 68 162 290), lower := (rows 19 38 76 137 280 33 68 128 256), losses := [] }

theorem u1130 : Upper (D 5) (R 5) [18,36,72,129,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1130
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 76 137 280 33 96 134 262), lower := (rows 19 38 76 137 280 33 96 128 256), losses := [] }

theorem u1131 : Upper (D 5) (R 5) [18,36,72,129,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 76 138 280 33 65 164 292), lower := (rows 19 38 76 138 280 33 65 128 256), losses := [] }

theorem u1132 : Upper (D 5) (R 5) [18,36,72,130,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 138 280 33 68 161 289), lower := (rows 19 38 76 138 280 33 68 128 256), losses := [] }

theorem u1133 : Upper (D 5) (R 5) [18,36,72,130,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 76 138 280 33 96 133 261), lower := (rows 19 38 76 138 280 33 96 128 256), losses := [] }

theorem u1134 : Upper (D 5) (R 5) [18,36,72,130,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0)], upper := (rows 19 38 76 140 25 288 65 162 290), lower := (rows 19 38 76 140 25 288 65 128 256), losses := [] }

theorem u1135 : Upper (D 5) (R 5) [18,36,72,132,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1136 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0)], upper := (rows 19 38 76 140 25 288 66 161 289), lower := (rows 19 38 76 140 25 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 288 67 128 256), good := (rows 86 102 76 140 92 288 66 128 288) }] }

theorem u1136 : Upper (D 5) (R 5) [18,36,72,132,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1137 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 153, targets := 32 }], pairs := [(0,5)], upper := (rows 19 38 76 140 25 288 96 131 259), lower := (rows 19 38 76 140 25 288 96 128 256), losses := [] }

theorem u1137 : Upper (D 5) (R 5) [18,36,72,132,9,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 76 140 280 33 65 162 290), lower := (rows 19 38 76 140 280 33 65 128 256), losses := [] }

theorem u1138 : Upper (D 5) (R 5) [18,36,72,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1)], upper := (rows 19 38 76 140 280 33 66 161 289), lower := (rows 19 38 76 140 280 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 10 19 33 64 161 289), good := (rows 441 444 76 140 280 433 92 128 256) }] }

theorem u1139 : Upper (D 5) (R 5) [18,36,72,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1139
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P05
