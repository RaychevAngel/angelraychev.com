import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 392 145 288 96 148 276), lower := (rows 35 67 76 392 145 288 96 128 256), losses := [] }

theorem u1140 : Upper (D 9) (R 9) [34,65,72,384,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1140 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1141 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 392 148 48 65 416 288), lower := (rows 35 67 76 392 148 48 65 128 256), losses := [] }

theorem u1141 : Upper (D 9) (R 9) [34,65,72,384,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1141 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1142 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 67 76 392 148 48 96 385 257), lower := (rows 35 67 76 392 148 48 96 128 256), losses := [] }

theorem u1142 : Upper (D 9) (R 9) [34,65,72,384,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1142 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(4,8)], upper := (rows 35 67 76 392 148 48 320 161 289), lower := (rows 35 67 76 392 148 48 320 128 256), losses := [] }

theorem u1143 : Upper (D 9) (R 9) [34,65,72,384,132,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1143 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 392 148 288 65 176 304), lower := (rows 35 67 76 392 148 288 65 128 256), losses := [] }

theorem u1144 : Upper (D 9) (R 9) [34,65,72,384,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1144 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 84, targets := 288 }], pairs := [(2,5),(2,8),(4,5),(4,8)], upper := (rows 35 67 76 392 148 288 80 161 289), lower := (rows 35 67 76 392 148 288 80 128 256), losses := [] }

theorem u1145 : Upper (D 9) (R 9) [34,65,72,384,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1145 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 76 392 148 288 96 145 273), lower := (rows 35 67 76 392 148 288 96 128 256), losses := [] }

theorem u1146 : Upper (D 9) (R 9) [34,65,72,384,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1146 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 440, targets := 65 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(3,0),(3,6),(4,0),(4,6)], upper := (rows 35 67 76 392 176 288 65 148 276), lower := (rows 35 67 76 392 176 288 65 128 256), losses := [] }

theorem u1147 : Upper (D 9) (R 9) [34,65,72,384,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1147 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 441, targets := 64 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 35 67 76 392 176 288 68 145 273), lower := (rows 35 67 76 392 176 288 68 128 256), losses := [] }

theorem u1148 : Upper (D 9) (R 9) [34,65,72,384,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1148 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 76 392 176 288 80 133 261), lower := (rows 35 67 76 392 176 288 80 128 256), losses := [] }

theorem u1149 : Upper (D 9) (R 9) [34,65,72,384,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1149 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 100 140 280 288 65 144 400), lower := (rows 35 67 100 140 280 288 65 128 256), losses := [] }

theorem u1150 : Upper (D 9) (R 9) [34,65,96,132,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1150 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1151 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 35 67 100 140 280 288 80 129 385), lower := (rows 35 67 100 140 280 288 80 128 256), losses := [] }

theorem u1151 : Upper (D 9) (R 9) [34,65,96,132,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1151 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,0)], upper := (rows 35 67 100 140 280 288 192 145 273), lower := (rows 35 67 100 140 280 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 304 200 128 256), good := (rows 34 66 100 204 380 288 192 192 288) }] }

theorem u1152 : Upper (D 9) (R 9) [34,65,96,132,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1152 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 67 100 140 400 288 65 152 280), lower := (rows 35 67 100 140 400 288 65 128 256), losses := [] }

theorem u1153 : Upper (D 9) (R 9) [34,65,96,132,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1153 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 100 140 400 288 72 145 273), lower := (rows 35 67 100 140 400 288 72 128 256), losses := [] }

theorem u1154 : Upper (D 9) (R 9) [34,65,96,132,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1154 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 35 67 100 140 400 288 80 137 265), lower := (rows 35 67 100 140 400 288 80 128 256), losses := [] }

theorem u1155 : Upper (D 9) (R 9) [34,65,96,132,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1155 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 152 276 288 72 224 352), lower := (rows 35 67 133 152 276 288 72 128 256), losses := [] }

theorem u1156 : Upper (D 9) (R 9) [34,65,129,144,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1156 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 133 152 276 288 96 200 328), lower := (rows 35 67 133 152 276 288 96 128 256), losses := [] }

theorem u1157 : Upper (D 9) (R 9) [34,65,129,144,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1157 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 133 152 304 36 72 448 320), lower := (rows 35 67 133 152 304 36 72 128 256), losses := [] }

theorem u1158 : Upper (D 9) (R 9) [34,65,129,144,288,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1158 [(5,2),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 152 304 36 320 200 328), lower := (rows 35 67 133 152 304 36 320 128 256), losses := [] }

theorem u1159 : Upper (D 9) (R 9) [34,65,129,144,288,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1159 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 67 133 152 336 36 72 416 288), lower := (rows 35 67 133 152 336 36 72 128 256), losses := [] }

theorem u1160 : Upper (D 9) (R 9) [34,65,129,144,320,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1160 [(5,2),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 152 336 36 96 392 264), lower := (rows 35 67 133 152 336 36 96 128 256), losses := [] }

theorem u1161 : Upper (D 9) (R 9) [34,65,129,144,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1161 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 133 152 336 36 320 168 296), lower := (rows 35 67 133 152 336 36 320 128 256), losses := [] }

theorem u1162 : Upper (D 9) (R 9) [34,65,129,144,320,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1162 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 66, targets := 416 }], pairs := [(1,5),(1,7),(1,8)], upper := (rows 35 67 133 152 336 40 68 416 288), lower := (rows 35 67 133 152 336 40 68 128 256), losses := [] }

theorem u1163 : Upper (D 9) (R 9) [34,65,129,144,320,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1163 [(5,3),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 260, camps := [{ cop := 5, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 152 336 40 96 388 260), lower := (rows 35 67 133 152 336 40 96 128 256), losses := [] }

theorem u1164 : Upper (D 9) (R 9) [34,65,129,144,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1164 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 67 133 152 336 40 320 164 292), lower := (rows 35 67 133 152 336 40 320 128 256), losses := [] }

theorem u1165 : Upper (D 9) (R 9) [34,65,129,144,320,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1165 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 133 152 336 288 68 168 296), lower := (rows 35 67 133 152 336 288 68 128 256), losses := [] }

theorem u1166 : Upper (D 9) (R 9) [34,65,129,144,320,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1166 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 376, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 35 67 133 152 336 288 72 164 292), lower := (rows 35 67 133 152 336 288 72 128 256), losses := [] }

theorem u1167 : Upper (D 9) (R 9) [34,65,129,144,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1167 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 133 152 336 288 96 140 268), lower := (rows 35 67 133 152 336 288 96 128 256), losses := [] }

theorem u1168 : Upper (D 9) (R 9) [34,65,129,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1168 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 404, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 35 67 133 168 276 288 72 208 336), lower := (rows 35 67 133 168 276 288 72 128 256), losses := [] }

theorem u1169 : Upper (D 9) (R 9) [34,65,129,160,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1169 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 168 276 288 80 200 328), lower := (rows 35 67 133 168 276 288 80 128 256), losses := [] }

theorem u1170 : Upper (D 9) (R 9) [34,65,129,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1170 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 133 168 280 288 68 208 336), lower := (rows 35 67 133 168 280 288 68 128 256), losses := [] }

theorem u1171 : Upper (D 9) (R 9) [34,65,129,160,264,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1171 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 168 280 288 80 196 324), lower := (rows 35 67 133 168 280 288 80 128 256), losses := [] }

theorem u1172 : Upper (D 9) (R 9) [34,65,129,160,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1172 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 67 133 168 336 288 68 152 280), lower := (rows 35 67 133 168 336 288 68 128 256), losses := [] }

theorem u1173 : Upper (D 9) (R 9) [34,65,129,160,320,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1173 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 404, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 35 67 133 168 336 288 72 148 276), lower := (rows 35 67 133 168 336 288 72 128 256), losses := [] }

theorem u1174 : Upper (D 9) (R 9) [34,65,129,160,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1174 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 5, region := 83, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,6)], upper := (rows 35 67 133 168 336 288 80 140 268), lower := (rows 35 67 133 168 336 288 80 128 256), losses := [] }

theorem u1175 : Upper (D 9) (R 9) [34,65,129,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1175 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5)], upper := (rows 35 67 133 200 276 48 72 416 288), lower := (rows 35 67 133 200 276 48 72 128 256), losses := [] }

theorem u1176 : Upper (D 9) (R 9) [34,65,129,192,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1176 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 200 276 48 96 392 264), lower := (rows 35 67 133 200 276 48 96 128 256), losses := [] }

theorem u1177 : Upper (D 9) (R 9) [34,65,129,192,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1177 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 200 276 48 320 168 296), lower := (rows 35 67 133 200 276 48 320 128 256), losses := [] }

theorem u1178 : Upper (D 9) (R 9) [34,65,129,192,260,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1178 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 67 133 200 276 288 72 176 304), lower := (rows 35 67 133 200 276 288 72 128 256), losses := [] }

theorem u1179 : Upper (D 9) (R 9) [34,65,129,192,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1179 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 3, region := 291, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 200 276 288 80 168 296), lower := (rows 35 67 133 200 276 288 80 128 256), losses := [] }

theorem u1180 : Upper (D 9) (R 9) [34,65,129,192,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1180 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 133 200 276 288 96 152 280), lower := (rows 35 67 133 200 276 288 96 128 256), losses := [] }

theorem u1181 : Upper (D 9) (R 9) [34,65,129,192,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1181 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5)], upper := (rows 35 67 133 200 280 48 68 416 288), lower := (rows 35 67 133 200 280 48 68 128 256), losses := [] }

theorem u1182 : Upper (D 9) (R 9) [34,65,129,192,264,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1182 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 200 280 48 96 388 260), lower := (rows 35 67 133 200 280 48 96 128 256), losses := [] }

theorem u1183 : Upper (D 9) (R 9) [34,65,129,192,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1183 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 133 200 280 48 320 164 292), lower := (rows 35 67 133 200 280 48 320 128 256), losses := [] }

theorem u1184 : Upper (D 9) (R 9) [34,65,129,192,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1184 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 67 133 200 280 288 68 176 304), lower := (rows 35 67 133 200 280 288 68 128 256), losses := [] }

theorem u1185 : Upper (D 9) (R 9) [34,65,129,192,264,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1185 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 376, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 35 67 133 200 280 288 80 164 292), lower := (rows 35 67 133 200 280 288 80 128 256), losses := [] }

theorem u1186 : Upper (D 9) (R 9) [34,65,129,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1186 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 67, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 133 200 280 288 96 148 276), lower := (rows 35 67 133 200 280 288 96 128 256), losses := [] }

theorem u1187 : Upper (D 9) (R 9) [34,65,129,192,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 376, targets := 1 }], pairs := [(1,7),(3,0),(4,0),(4,6)], upper := (rows 35 67 133 268 304 160 72 208 336), lower := (rows 35 67 133 268 304 160 72 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 24 164 0 128 256), good := (rows 35 3 165 316 304 160 24 160 256) },{ target := 7, region := (rows 1 6 4 12 17 32 76 0 262), good := (rows 307 339 351 334 304 32 72 0 256) }] }

theorem u1188 : Upper (D 9) (R 9) [34,65,129,260,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1188 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 268 304 160 80 200 328), lower := (rows 35 67 133 268 304 160 80 128 256), losses := [] }

theorem u1189 : Upper (D 9) (R 9) [34,65,129,260,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1189 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1190 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 133 268 336 40 80 160 416), lower := (rows 35 67 133 268 336 40 80 128 256), losses := [] }

theorem u1190 : Upper (D 9) (R 9) [34,65,129,260,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1190 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1191 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 268 336 40 96 144 400), lower := (rows 35 67 133 268 336 40 96 128 256), losses := [] }

theorem u1191 : Upper (D 9) (R 9) [34,65,129,260,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1191 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 376, targets := 1 },{ cop := 2, region := 66, targets := 288 }], pairs := [(1,5),(1,8),(3,0),(4,0)], upper := (rows 35 67 133 268 336 40 192 176 304), lower := (rows 35 67 133 268 336 40 192 128 256), losses := [] }

theorem u1192 : Upper (D 9) (R 9) [34,65,129,260,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1192 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 167, targets := 256 },{ cop := 2, region := 376, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 67 133 268 336 160 72 176 304), lower := (rows 35 67 133 268 336 160 72 128 256), losses := [] }

theorem u1193 : Upper (D 9) (R 9) [34,65,129,260,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1193 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 8, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 67 133 268 336 160 80 168 296), lower := (rows 35 67 133 268 336 160 80 128 256), losses := [] }

theorem u1194 : Upper (D 9) (R 9) [34,65,129,260,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1194 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 3, targets := 384 },{ cop := 1, region := 412, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,5)], upper := (rows 35 67 133 268 336 160 96 152 280), lower := (rows 35 67 133 268 336 160 96 128 256), losses := [] }

theorem u1195 : Upper (D 9) (R 9) [34,65,129,260,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1196 : Route 9 := (fun mask => (mask,id))

def c1196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1196 : Upper (D 9) (R 9) [34,65,129,260,384,8,16] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,384,8,16] 13 (by decide) (choices 1) [32,64] r1196 c1196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u47
  · exact u48

def b1197 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 268 400 40 96 208 336), lower := (rows 35 67 133 268 400 40 96 128 256), losses := [] }

theorem u1197 : Upper (D 9) (R 9) [34,65,129,260,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1197 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1198 : Route 9 := (fun mask => (mask,id))

def c1198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1198 : Upper (D 9) (R 9) [34,65,129,260,384,16,8] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260,384,16,8] 13 (by decide) (choices 1) [32,64] r1198 c1198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u49
  · exact u50

def b1199 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 67 133 268 400 48 96 200 328), lower := (rows 35 67 133 268 400 48 96 128 256), losses := [] }

theorem u1199 : Upper (D 9) (R 9) [34,65,129,260,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1199 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P09
