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

def b7080 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 56 146 288 65 130 386), lower := (rows 37 74 69 56 146 288 65 128 256), losses := [] }

theorem u7080 : Upper (D 7) (R 7) [36,72,65,48,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7080 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7081 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 56 146 288 66 129 385), lower := (rows 37 74 69 56 146 288 66 128 256), losses := [] }

theorem u7081 : Upper (D 7) (R 7) [36,72,65,48,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7081 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7082 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 74 69 56 146 288 192 131 259), lower := (rows 37 74 69 56 146 288 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 288 208 128 256), good := (rows 36 74 68 122 210 288 192 192 288) }] }

theorem u7082 : Upper (D 7) (R 7) [36,72,65,48,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7082 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7083 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 74 69 56 273 160 66 130 386), lower := (rows 37 74 69 56 273 160 66 128 256), losses := [] }

theorem u7083 : Upper (D 7) (R 7) [36,72,65,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7084 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 69 56 273 160 192 130 258), lower := (rows 37 74 69 56 273 160 192 128 256), losses := [] }

theorem u7084 : Upper (D 7) (R 7) [36,72,65,48,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7085 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 56 274 160 65 130 386), lower := (rows 37 74 69 56 274 160 65 128 256), losses := [] }

theorem u7085 : Upper (D 7) (R 7) [36,72,65,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7086 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 1, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 74 69 56 274 160 66 129 385), lower := (rows 37 74 69 56 274 160 66 128 256), losses := [] }

theorem u7086 : Upper (D 7) (R 7) [36,72,65,48,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7087 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(2,1)], upper := (rows 37 74 69 56 274 160 192 131 259), lower := (rows 37 74 69 56 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 100 122 274 224 224 224 256) },{ target := 5, region := (rows 1 10 5 8 16 0 224 128 256), good := (rows 69 74 69 90 274 192 192 192 256) }] }

theorem u7087 : Upper (D 7) (R 7) [36,72,65,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7088 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 56 400 34 65 130 386), lower := (rows 37 74 69 56 400 34 65 128 256), losses := [] }

theorem u7088 : Upper (D 7) (R 7) [36,72,65,48,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7089 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 69 56 400 34 66 129 385), lower := (rows 37 74 69 56 400 34 66 128 256), losses := [] }

theorem u7089 : Upper (D 7) (R 7) [36,72,65,48,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7090 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 69 56 400 34 192 131 259), lower := (rows 37 74 69 56 400 34 192 128 256), losses := [] }

theorem u7090 : Upper (D 7) (R 7) [36,72,65,48,384,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7091 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 138 50 288 65 144 400), lower := (rows 37 74 69 138 50 288 65 128 256), losses := [] }

theorem u7091 : Upper (D 7) (R 7) [36,72,65,130,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7091 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7092 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 421, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 74 69 138 50 288 80 129 385), lower := (rows 37 74 69 138 50 288 80 128 256), losses := [] }

theorem u7092 : Upper (D 7) (R 7) [36,72,65,130,34,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7092 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7093 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 69 138 50 288 192 145 273), lower := (rows 37 74 69 138 50 288 192 128 256), losses := [] }

theorem u7093 : Upper (D 7) (R 7) [36,72,65,130,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7093 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7094 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 69 138 145 288 66 176 304), lower := (rows 37 74 69 138 145 288 66 128 256), losses := [] }

theorem u7094 : Upper (D 7) (R 7) [36,72,65,130,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7094 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7095 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 37 74 69 138 145 288 80 162 290), lower := (rows 37 74 69 138 145 288 80 128 256), losses := [] }

theorem u7095 : Upper (D 7) (R 7) [36,72,65,130,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7095 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7096 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 138 145 288 96 146 274), lower := (rows 37 74 69 138 145 288 96 128 256), losses := [] }

theorem u7096 : Upper (D 7) (R 7) [36,72,65,130,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7096 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7097 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 138 176 288 65 146 274), lower := (rows 37 74 69 138 176 288 65 128 256), losses := [] }

theorem u7097 : Upper (D 7) (R 7) [36,72,65,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7097 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7098 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 69 138 176 288 66 145 273), lower := (rows 37 74 69 138 176 288 66 128 256), losses := [] }

theorem u7098 : Upper (D 7) (R 7) [36,72,65,130,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7098 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7099 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 37 74 69 138 176 288 80 131 259), lower := (rows 37 74 69 138 176 288 80 128 256), losses := [] }

theorem u7099 : Upper (D 7) (R 7) [36,72,65,130,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7099 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7100 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 69 138 273 48 66 160 416), lower := (rows 37 74 69 138 273 48 66 128 256), losses := [] }

theorem u7100 : Upper (D 7) (R 7) [36,72,65,130,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7100 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7101 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 117, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 138 273 48 96 130 386), lower := (rows 37 74 69 138 273 48 96 128 256), losses := [] }

theorem u7101 : Upper (D 7) (R 7) [36,72,65,130,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7101 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7102 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 69 138 273 48 192 162 290), lower := (rows 37 74 69 138 273 48 192 128 256), losses := [] }

theorem u7102 : Upper (D 7) (R 7) [36,72,65,130,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7102 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7103 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 138 274 48 65 160 416), lower := (rows 37 74 69 138 274 48 65 128 256), losses := [] }

theorem u7103 : Upper (D 7) (R 7) [36,72,65,130,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7103 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7104 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 37 74 69 138 274 48 96 129 385), lower := (rows 37 74 69 138 274 48 96 128 256), losses := [] }

theorem u7104 : Upper (D 7) (R 7) [36,72,65,130,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7104 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7105 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 69 138 274 48 192 161 289), lower := (rows 37 74 69 138 274 48 192 128 256), losses := [] }

theorem u7105 : Upper (D 7) (R 7) [36,72,65,130,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7105 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7106 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 138 274 160 65 176 304), lower := (rows 37 74 69 138 274 160 65 128 256), losses := [] }

theorem u7106 : Upper (D 7) (R 7) [36,72,65,130,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7107 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 69 138 274 160 80 161 289), lower := (rows 37 74 69 138 274 160 80 128 256), losses := [] }

theorem u7107 : Upper (D 7) (R 7) [36,72,65,130,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7107 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7108 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 138 274 160 96 145 273), lower := (rows 37 74 69 138 274 160 96 128 256), losses := [] }

theorem u7108 : Upper (D 7) (R 7) [36,72,65,130,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7109 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 138 304 160 65 146 274), lower := (rows 37 74 69 138 304 160 65 128 256), losses := [] }

theorem u7109 : Upper (D 7) (R 7) [36,72,65,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7110 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 69 138 304 160 66 145 273), lower := (rows 37 74 69 138 304 160 66 128 256), losses := [] }

theorem u7110 : Upper (D 7) (R 7) [36,72,65,130,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7111 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 138 304 160 80 131 259), lower := (rows 37 74 69 138 304 160 80 128 256), losses := [] }

theorem u7111 : Upper (D 7) (R 7) [36,72,65,130,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7111 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7112 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 138 400 48 65 162 290), lower := (rows 37 74 69 138 400 48 65 128 256), losses := [] }

theorem u7112 : Upper (D 7) (R 7) [36,72,65,130,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7113 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 69 138 400 48 66 161 289), lower := (rows 37 74 69 138 400 48 66 128 256), losses := [] }

theorem u7113 : Upper (D 7) (R 7) [36,72,65,130,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7113 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7114 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 69 138 400 48 96 131 259), lower := (rows 37 74 69 138 400 48 96 128 256), losses := [] }

theorem u7114 : Upper (D 7) (R 7) [36,72,65,130,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7114 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7115 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 152 50 288 65 130 386), lower := (rows 37 74 69 152 50 288 65 128 256), losses := [] }

theorem u7115 : Upper (D 7) (R 7) [36,72,65,144,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7115 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7116 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 69 152 50 288 66 129 385), lower := (rows 37 74 69 152 50 288 66 128 256), losses := [] }

theorem u7116 : Upper (D 7) (R 7) [36,72,65,144,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7116 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7117 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 69 152 50 288 192 131 259), lower := (rows 37 74 69 152 50 288 192 128 256), losses := [] }

theorem u7117 : Upper (D 7) (R 7) [36,72,65,144,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7117 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7118 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 152 274 160 65 162 290), lower := (rows 37 74 69 152 274 160 65 128 256), losses := [] }

theorem u7118 : Upper (D 7) (R 7) [36,72,65,144,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7119 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 2 },{ cop := 3, region := 66, targets := 160 }], pairs := [(0,1),(1,5),(1,7),(2,1)], upper := (rows 37 74 69 152 274 160 66 161 289), lower := (rows 37 74 69 152 274 160 66 128 256), losses := [] }

theorem u7119 : Upper (D 7) (R 7) [36,72,65,144,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7120 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 69 152 274 160 96 131 259), lower := (rows 37 74 69 152 274 160 96 128 256), losses := [] }

theorem u7120 : Upper (D 7) (R 7) [36,72,65,144,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7121 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 152 304 34 65 130 386), lower := (rows 37 74 69 152 304 34 65 128 256), losses := [] }

theorem u7121 : Upper (D 7) (R 7) [36,72,65,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7122 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 69 152 304 34 66 129 385), lower := (rows 37 74 69 152 304 34 66 128 256), losses := [] }

theorem u7122 : Upper (D 7) (R 7) [36,72,65,144,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7123 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 69 152 304 34 192 131 259), lower := (rows 37 74 69 152 304 34 192 128 256), losses := [] }

theorem u7123 : Upper (D 7) (R 7) [36,72,65,144,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7124 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 152 304 160 65 130 258), lower := (rows 37 74 69 152 304 160 65 128 256), losses := [] }

theorem u7124 : Upper (D 7) (R 7) [36,72,65,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7125 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 160 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(1,5),(1,7)], upper := (rows 37 74 69 152 304 160 66 131 259), lower := (rows 37 74 69 152 304 160 66 128 256), losses := [{ target := 1, region := (rows 3 0 70 8 16 168 64 128 256), good := (rows 37 109 69 184 304 160 69 160 256) }] }

theorem u7125 : Upper (D 7) (R 7) [36,72,65,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7126 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 168 145 288 66 146 274), lower := (rows 37 74 69 168 145 288 66 128 256), losses := [] }

theorem u7126 : Upper (D 7) (R 7) [36,72,65,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7126 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7127 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 74 69 168 145 288 80 130 258), lower := (rows 37 74 69 168 145 288 80 128 256), losses := [] }

theorem u7127 : Upper (D 7) (R 7) [36,72,65,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7127 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7128 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 168 146 288 65 146 274), lower := (rows 37 74 69 168 146 288 65 128 256), losses := [] }

theorem u7128 : Upper (D 7) (R 7) [36,72,65,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7128 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7129 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 74 69 168 146 288 66 145 273), lower := (rows 37 74 69 168 146 288 66 128 256), losses := [] }

theorem u7129 : Upper (D 7) (R 7) [36,72,65,160,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7129 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7130 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 37 74 69 168 146 288 80 131 259), lower := (rows 37 74 69 168 146 288 80 128 256), losses := [] }

theorem u7130 : Upper (D 7) (R 7) [36,72,65,160,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7130 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7131 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 168 274 34 65 144 400), lower := (rows 37 74 69 168 274 34 65 128 256), losses := [] }

theorem u7131 : Upper (D 7) (R 7) [36,72,65,160,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7132 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 1, region := 37, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 37 74 69 168 274 34 80 129 385), lower := (rows 37 74 69 168 274 34 80 128 256), losses := [] }

theorem u7132 : Upper (D 7) (R 7) [36,72,65,160,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7132 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7133 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 69, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 69 168 274 34 192 145 273), lower := (rows 37 74 69 168 274 34 192 128 256), losses := [] }

theorem u7133 : Upper (D 7) (R 7) [36,72,65,160,258,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7134 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 37 74 69 168 274 48 65 130 386), lower := (rows 37 74 69 168 274 48 65 128 256), losses := [] }

theorem u7134 : Upper (D 7) (R 7) [36,72,65,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7134 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7135 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 69 168 274 48 66 129 385), lower := (rows 37 74 69 168 274 48 66 128 256), losses := [] }

theorem u7135 : Upper (D 7) (R 7) [36,72,65,160,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7135 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7136 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 69 168 274 48 192 131 259), lower := (rows 37 74 69 168 274 48 192 128 256), losses := [] }

theorem u7136 : Upper (D 7) (R 7) [36,72,65,160,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7136 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7137 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 65 }], pairs := [(3,0),(3,6),(4,0),(4,6)], upper := (rows 37 74 69 168 400 34 65 146 274), lower := (rows 37 74 69 168 400 34 65 128 256), losses := [] }

theorem u7137 : Upper (D 7) (R 7) [36,72,65,160,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7138 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 69 168 400 34 66 145 273), lower := (rows 37 74 69 168 400 34 66 128 256), losses := [] }

theorem u7138 : Upper (D 7) (R 7) [36,72,65,160,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7139 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 74 69 168 400 34 80 131 259), lower := (rows 37 74 69 168 400 34 80 128 256), losses := [] }

theorem u7139 : Upper (D 7) (R 7) [36,72,65,160,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7139 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7139
end Delivery.IrregularNine14.P07
