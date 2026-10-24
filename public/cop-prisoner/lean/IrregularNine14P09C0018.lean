import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 35 67 44 200 400 288 80 133 261), lower := (rows 35 67 44 200 400 288 80 128 256), losses := [] }

theorem u1080 : Upper (D 9) (R 9) [34,65,40,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1080 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 70, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 137 176 288 68 400 272), lower := (rows 35 67 76 137 176 288 68 128 256), losses := [] }

theorem u1081 : Upper (D 9) (R 9) [34,65,72,129,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1081 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 76 137 176 288 80 388 260), lower := (rows 35 67 76 137 176 288 80 128 256), losses := [] }

theorem u1082 : Upper (D 9) (R 9) [34,65,72,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1082 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 5, region := 67, targets := 128 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,7),(1,7),(2,0),(4,0),(4,6)], upper := (rows 35 67 76 137 176 288 320 148 276), lower := (rows 35 67 76 137 176 288 320 128 256), losses := [] }

theorem u1083 : Upper (D 9) (R 9) [34,65,72,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1083 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,0)], upper := (rows 35 67 76 137 276 288 80 160 416), lower := (rows 35 67 76 137 276 288 80 128 256), losses := [] }

theorem u1084 : Upper (D 9) (R 9) [34,65,72,129,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1084 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 137 276 288 96 144 400), lower := (rows 35 67 76 137 276 288 96 128 256), losses := [] }

theorem u1085 : Upper (D 9) (R 9) [34,65,72,129,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1085 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 288 },{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 67 76 137 276 288 192 176 304), lower := (rows 35 67 76 137 276 288 192 128 256), losses := [] }

theorem u1086 : Upper (D 9) (R 9) [34,65,72,129,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1086 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 70, targets := 416 }], pairs := [(1,5),(1,7),(1,8)], upper := (rows 35 67 76 137 400 48 68 416 288), lower := (rows 35 67 76 137 400 48 68 128 256), losses := [] }

theorem u1087 : Upper (D 9) (R 9) [34,65,72,129,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1087 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 76 137 400 48 96 388 260), lower := (rows 35 67 76 137 400 48 96 128 256), losses := [] }

theorem u1088 : Upper (D 9) (R 9) [34,65,72,129,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1088 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 76 137 400 48 320 164 292), lower := (rows 35 67 76 137 400 48 320 128 256), losses := [] }

theorem u1089 : Upper (D 9) (R 9) [34,65,72,129,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1089 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 137 400 288 68 176 304), lower := (rows 35 67 76 137 400 288 68 128 256), losses := [] }

theorem u1090 : Upper (D 9) (R 9) [34,65,72,129,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1090 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 35 67 76 137 400 288 80 164 292), lower := (rows 35 67 76 137 400 288 80 128 256), losses := [] }

theorem u1091 : Upper (D 9) (R 9) [34,65,72,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1091 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 137 400 288 96 148 276), lower := (rows 35 67 76 137 400 288 96 128 256), losses := [] }

theorem u1092 : Upper (D 9) (R 9) [34,65,72,129,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1092 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 140 176 288 65 400 272), lower := (rows 35 67 76 140 176 288 65 128 256), losses := [] }

theorem u1093 : Upper (D 9) (R 9) [34,65,72,132,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1093 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 67 76 140 176 288 80 385 257), lower := (rows 35 67 76 140 176 288 80 128 256), losses := [] }

theorem u1094 : Upper (D 9) (R 9) [34,65,72,132,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1094 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 323, targets := 128 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(0,7),(1,7),(4,6),(4,8)], upper := (rows 35 67 76 140 176 288 320 145 273), lower := (rows 35 67 76 140 176 288 320 128 256), losses := [] }

theorem u1095 : Upper (D 9) (R 9) [34,65,72,132,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1095 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 83, targets := 128 },{ cop := 1, region := 428, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 76 140 273 288 80 160 416), lower := (rows 35 67 76 140 273 288 80 128 256), losses := [] }

theorem u1096 : Upper (D 9) (R 9) [34,65,72,132,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1096 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 140 273 288 96 144 400), lower := (rows 35 67 76 140 273 288 96 128 256), losses := [] }

theorem u1097 : Upper (D 9) (R 9) [34,65,72,132,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1097 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 12, targets := 289 }], pairs := [(2,0),(2,5),(2,8),(3,0),(3,5)], upper := (rows 35 67 76 140 273 288 192 176 304), lower := (rows 35 67 76 140 273 288 192 128 256), losses := [] }

theorem u1098 : Upper (D 9) (R 9) [34,65,72,132,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1098 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 140 400 288 65 176 304), lower := (rows 35 67 76 140 400 288 65 128 256), losses := [] }

theorem u1099 : Upper (D 9) (R 9) [34,65,72,132,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1099 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 35 67 76 140 400 288 80 161 289), lower := (rows 35 67 76 140 400 288 80 128 256), losses := [] }

theorem u1100 : Upper (D 9) (R 9) [34,65,72,132,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1100 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 140 400 288 96 145 273), lower := (rows 35 67 76 140 400 288 96 128 256), losses := [] }

theorem u1101 : Upper (D 9) (R 9) [34,65,72,132,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 441, targets := 64 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,6),(0,8),(3,6),(4,6)], upper := (rows 35 67 76 152 273 160 68 416 288), lower := (rows 35 67 76 152 273 160 68 128 256), losses := [] }

theorem u1102 : Upper (D 9) (R 9) [34,65,72,144,257,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1102 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 152 273 160 96 388 260), lower := (rows 35 67 76 152 273 160 96 128 256), losses := [] }

theorem u1103 : Upper (D 9) (R 9) [34,65,72,144,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1103 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 163, targets := 256 },{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,0),(3,0)], upper := (rows 35 67 76 152 273 160 320 164 292), lower := (rows 35 67 76 152 273 160 320 128 256), losses := [] }

theorem u1104 : Upper (D 9) (R 9) [34,65,72,144,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1104 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1105 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 441, targets := 64 },{ cop := 3, region := 68, targets := 32 }], pairs := [(0,6),(2,5),(3,6),(4,6)], upper := (rows 35 67 76 152 273 288 68 160 416), lower := (rows 35 67 76 152 273 288 68 128 256), losses := [] }

theorem u1105 : Upper (D 9) (R 9) [34,65,72,144,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1105 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 132, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 152 273 288 96 132 388), lower := (rows 35 67 76 152 273 288 96 128 256), losses := [] }

theorem u1106 : Upper (D 9) (R 9) [34,65,72,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 288 }], pairs := [(0,7),(1,7),(2,5),(2,8),(4,7)], upper := (rows 35 67 76 152 273 288 192 164 292), lower := (rows 35 67 76 152 273 288 192 128 256), losses := [] }

theorem u1107 : Upper (D 9) (R 9) [34,65,72,144,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1107 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 6, region := 2, targets := 32 }], pairs := [(1,5),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 152 276 288 65 160 416), lower := (rows 35 67 76 152 276 288 65 128 256), losses := [] }

theorem u1108 : Upper (D 9) (R 9) [34,65,72,144,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 76 152 276 288 96 129 385), lower := (rows 35 67 76 152 276 288 96 128 256), losses := [] }

theorem u1109 : Upper (D 9) (R 9) [34,65,72,144,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1109 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 68, targets := 33 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,7)], upper := (rows 35 67 76 152 276 288 192 161 289), lower := (rows 35 67 76 152 276 288 192 128 256), losses := [] }

theorem u1110 : Upper (D 9) (R 9) [34,65,72,144,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 152 304 160 65 388 260), lower := (rows 35 67 76 152 304 160 65 128 256), losses := [] }

theorem u1111 : Upper (D 9) (R 9) [34,65,72,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1111 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 441, targets := 64 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,6),(0,8),(3,6),(4,6)], upper := (rows 35 67 76 152 304 160 68 385 257), lower := (rows 35 67 76 152 304 160 68 128 256), losses := [] }

theorem u1112 : Upper (D 9) (R 9) [34,65,72,144,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1112 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 163, targets := 256 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 152 304 160 320 133 261), lower := (rows 35 67 76 152 304 160 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 168 336 128 256), good := (rows 34 66 108 252 368 160 320 160 320) }] }

theorem u1113 : Upper (D 9) (R 9) [34,65,72,144,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1113 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 76 168 145 288 68 400 272), lower := (rows 35 67 76 168 145 288 68 128 256), losses := [] }

theorem u1114 : Upper (D 9) (R 9) [34,65,72,160,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1114 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 76 168 145 288 80 388 260), lower := (rows 35 67 76 168 145 288 80 128 256), losses := [] }

theorem u1115 : Upper (D 9) (R 9) [34,65,72,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1115 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 364, targets := 1 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,0),(3,0)], upper := (rows 35 67 76 168 145 288 320 148 276), lower := (rows 35 67 76 168 145 288 320 128 256), losses := [{ target := 5, region := (rows 1 3 12 8 16 0 352 128 256), good := (rows 67 67 76 204 147 320 320 128 320) }] }

theorem u1116 : Upper (D 9) (R 9) [34,65,72,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1116 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,8),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 168 148 288 65 400 272), lower := (rows 35 67 76 168 148 288 65 128 256), losses := [] }

theorem u1117 : Upper (D 9) (R 9) [34,65,72,160,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1117 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 67 76 168 148 288 80 385 257), lower := (rows 35 67 76 168 148 288 80 128 256), losses := [] }

theorem u1118 : Upper (D 9) (R 9) [34,65,72,160,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1118 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(2,0),(4,0)], upper := (rows 35 67 76 168 148 288 320 145 273), lower := (rows 35 67 76 168 148 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 352 352 128 256), good := (rows 98 98 124 252 148 352 352 128 352) },{ target := 5, region := (rows 1 3 12 8 24 0 352 128 256), good := (rows 67 67 92 220 148 320 320 128 320) }] }

theorem u1119 : Upper (D 9) (R 9) [34,65,72,160,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1119 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7)], upper := (rows 35 67 76 168 273 48 68 384 384), lower := (rows 35 67 76 168 273 48 68 128 256), losses := [] }

theorem u1120 : Upper (D 9) (R 9) [34,65,72,160,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1120 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 35 67 76 168 273 48 192 388 260), lower := (rows 35 67 76 168 273 48 192 128 256), losses := [] }

theorem u1121 : Upper (D 9) (R 9) [34,65,72,160,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1121 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 132, camps := [{ cop := 6, region := 51, targets := 128 },{ cop := 0, region := 460, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 76 168 273 48 320 132 388), lower := (rows 35 67 76 168 273 48 320 128 256), losses := [] }

theorem u1122 : Upper (D 9) (R 9) [34,65,72,160,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1122 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 168 273 288 68 144 400), lower := (rows 35 67 76 168 273 288 68 128 256), losses := [] }

theorem u1123 : Upper (D 9) (R 9) [34,65,72,160,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1123 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 132, camps := [{ cop := 5, region := 83, targets := 128 },{ cop := 1, region := 428, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 76 168 273 288 80 132 388), lower := (rows 35 67 76 168 273 288 80 128 256), losses := [] }

theorem u1124 : Upper (D 9) (R 9) [34,65,72,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1124 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 76 168 273 288 192 148 276), lower := (rows 35 67 76 168 273 288 192 128 256), losses := [] }

theorem u1125 : Upper (D 9) (R 9) [34,65,72,160,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1125 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 168 276 48 65 384 384), lower := (rows 35 67 76 168 276 48 65 128 256), losses := [] }

theorem u1126 : Upper (D 9) (R 9) [34,65,72,160,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1126 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 35 67 76 168 276 48 192 385 257), lower := (rows 35 67 76 168 276 48 192 128 256), losses := [] }

theorem u1127 : Upper (D 9) (R 9) [34,65,72,160,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1127 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 99, targets := 128 },{ cop := 0, region := 450, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,7),(1,5),(1,7),(3,6)], upper := (rows 35 67 76 168 276 48 320 129 385), lower := (rows 35 67 76 168 276 48 320 128 256), losses := [] }

theorem u1128 : Upper (D 9) (R 9) [34,65,72,160,260,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1128 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 76 168 276 288 65 144 400), lower := (rows 35 67 76 168 276 288 65 128 256), losses := [] }

theorem u1129 : Upper (D 9) (R 9) [34,65,72,160,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1129 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,6)], upper := (rows 35 67 76 168 276 288 80 129 385), lower := (rows 35 67 76 168 276 288 80 128 256), losses := [] }

theorem u1130 : Upper (D 9) (R 9) [34,65,72,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1130 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 67 76 168 276 288 192 145 273), lower := (rows 35 67 76 168 276 288 192 128 256), losses := [] }

theorem u1131 : Upper (D 9) (R 9) [34,65,72,160,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1131 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 76 168 400 288 65 148 276), lower := (rows 35 67 76 168 400 288 65 128 256), losses := [] }

theorem u1132 : Upper (D 9) (R 9) [34,65,72,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1132 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 168 400 288 68 145 273), lower := (rows 35 67 76 168 400 288 68 128 256), losses := [] }

theorem u1133 : Upper (D 9) (R 9) [34,65,72,160,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1133 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 4, region := 108, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,0)], upper := (rows 35 67 76 168 400 288 80 133 261), lower := (rows 35 67 76 168 400 288 80 128 256), losses := [] }

theorem u1134 : Upper (D 9) (R 9) [34,65,72,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1134 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 76 392 145 48 68 416 288), lower := (rows 35 67 76 392 145 48 68 128 256), losses := [] }

theorem u1135 : Upper (D 9) (R 9) [34,65,72,384,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1135 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1136 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 76 392 145 48 96 388 260), lower := (rows 35 67 76 392 145 48 96 128 256), losses := [] }

theorem u1136 : Upper (D 9) (R 9) [34,65,72,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1136 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1137 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(4,8)], upper := (rows 35 67 76 392 145 48 320 164 292), lower := (rows 35 67 76 392 145 48 320 128 256), losses := [] }

theorem u1137 : Upper (D 9) (R 9) [34,65,72,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1137 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 441, targets := 64 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 35 67 76 392 145 288 68 176 304), lower := (rows 35 67 76 392 145 288 68 128 256), losses := [] }

theorem u1138 : Upper (D 9) (R 9) [34,65,72,384,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1138 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 66, targets := 416 },{ cop := 1, region := 428, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(2,0)], upper := (rows 35 67 76 392 145 288 80 164 292), lower := (rows 35 67 76 392 145 288 80 128 256), losses := [] }

theorem u1139 : Upper (D 9) (R 9) [34,65,72,384,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1139 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P09
