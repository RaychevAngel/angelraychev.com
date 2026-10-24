import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7140 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 134 261 26 81 96 72 164 292), lower := (rows 35 134 261 26 81 96 72 128 256), losses := [] }

theorem u7140 : Upper (D 6) (R 6) [34,132,257,18,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7140 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7141 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 261 26 81 96 96 140 268), lower := (rows 35 134 261 26 81 96 96 128 256), losses := [] }

theorem u7141 : Upper (D 6) (R 6) [34,132,257,18,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7142 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 170, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(3,0)], upper := (rows 35 134 261 26 84 96 65 168 296), lower := (rows 35 134 261 26 84 96 65 128 256), losses := [] }

theorem u7142 : Upper (D 6) (R 6) [34,132,257,18,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7143 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 26 84 96 72 161 289), lower := (rows 35 134 261 26 84 96 72 128 256), losses := [] }

theorem u7143 : Upper (D 6) (R 6) [34,132,257,18,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7143 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7144 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 1, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 134 261 26 84 96 96 137 265), lower := (rows 35 134 261 26 84 96 96 128 256), losses := [] }

theorem u7144 : Upper (D 6) (R 6) [34,132,257,18,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7145 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 261 28 81 96 66 168 296), lower := (rows 35 134 261 28 81 96 66 128 256), losses := [] }

theorem u7145 : Upper (D 6) (R 6) [34,132,257,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7145 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7146 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 28 81 96 72 162 290), lower := (rows 35 134 261 28 81 96 72 128 256), losses := [] }

theorem u7146 : Upper (D 6) (R 6) [34,132,257,20,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7146 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7147 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 261 28 81 96 96 138 266), lower := (rows 35 134 261 28 81 96 96 128 256), losses := [] }

theorem u7147 : Upper (D 6) (R 6) [34,132,257,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7148 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 261 28 82 96 65 168 296), lower := (rows 35 134 261 28 82 96 65 128 256), losses := [] }

theorem u7148 : Upper (D 6) (R 6) [34,132,257,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7149 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 28 82 96 72 161 289), lower := (rows 35 134 261 28 82 96 72 128 256), losses := [] }

theorem u7149 : Upper (D 6) (R 6) [34,132,257,20,66,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7149 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7150 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(3,0),(4,0)], upper := (rows 35 134 261 28 82 96 96 137 265), lower := (rows 35 134 261 28 82 96 96 128 256), losses := [] }

theorem u7150 : Upper (D 6) (R 6) [34,132,257,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7151 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 261 44 81 96 66 152 280), lower := (rows 35 134 261 44 81 96 66 128 256), losses := [] }

theorem u7151 : Upper (D 6) (R 6) [34,132,257,36,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7152 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 35 134 261 44 81 96 72 146 274), lower := (rows 35 134 261 44 81 96 72 128 256), losses := [] }

theorem u7152 : Upper (D 6) (R 6) [34,132,257,36,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7152 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7153 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 44 81 96 80 138 266), lower := (rows 35 134 261 44 81 96 80 128 256), losses := [] }

theorem u7153 : Upper (D 6) (R 6) [34,132,257,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7153 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7154 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 261 44 82 96 65 152 280), lower := (rows 35 134 261 44 82 96 65 128 256), losses := [] }

theorem u7154 : Upper (D 6) (R 6) [34,132,257,36,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7155 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 134 261 44 82 96 72 145 273), lower := (rows 35 134 261 44 82 96 72 128 256), losses := [] }

theorem u7155 : Upper (D 6) (R 6) [34,132,257,36,66,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7155 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7156 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 261 44 82 96 80 137 265), lower := (rows 35 134 261 44 82 96 80 128 256), losses := [] }

theorem u7156 : Upper (D 6) (R 6) [34,132,257,36,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7156 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7157 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 120, targets := 2 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(3,1),(4,1)], upper := (rows 35 134 261 44 88 96 65 146 274), lower := (rows 35 134 261 44 88 96 65 128 256), losses := [] }

theorem u7157 : Upper (D 6) (R 6) [34,132,257,36,72,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7158 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(3,0),(4,0)], upper := (rows 35 134 261 44 88 96 66 145 273), lower := (rows 35 134 261 44 88 96 66 128 256), losses := [] }

theorem u7158 : Upper (D 6) (R 6) [34,132,257,36,72,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7159 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 261 44 88 96 80 131 259), lower := (rows 35 134 261 44 88 96 80 128 256), losses := [] }

theorem u7159 : Upper (D 6) (R 6) [34,132,257,36,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7159 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7160 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 134 261 73 84 40 66 176 304), lower := (rows 35 134 261 73 84 40 66 128 256), losses := [] }

theorem u7160 : Upper (D 6) (R 6) [34,132,257,65,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7160 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7161 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 134 261 73 84 40 80 162 290), lower := (rows 35 134 261 73 84 40 80 128 256), losses := [] }

theorem u7161 : Upper (D 6) (R 6) [34,132,257,65,68,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7161 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7162 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 73 84 40 96 146 274), lower := (rows 35 134 261 73 84 40 96 128 256), losses := [] }

theorem u7162 : Upper (D 6) (R 6) [34,132,257,65,68,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7162 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7163 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 261 73 84 48 66 168 296), lower := (rows 35 134 261 73 84 48 66 128 256), losses := [] }

theorem u7163 : Upper (D 6) (R 6) [34,132,257,65,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7163 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7164 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 134 261 73 84 48 72 162 290), lower := (rows 35 134 261 73 84 48 72 128 256), losses := [] }

theorem u7164 : Upper (D 6) (R 6) [34,132,257,65,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7164 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7165 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 73 84 48 96 138 266), lower := (rows 35 134 261 73 84 48 96 128 256), losses := [] }

theorem u7165 : Upper (D 6) (R 6) [34,132,257,65,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7165 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7166 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 134 261 74 84 33 72 176 304), lower := (rows 35 134 261 74 84 33 72 128 256), losses := [] }

theorem u7166 : Upper (D 6) (R 6) [34,132,257,66,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7166 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7167 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 134 261 74 84 33 80 168 296), lower := (rows 35 134 261 74 84 33 80 128 256), losses := [] }

theorem u7167 : Upper (D 6) (R 6) [34,132,257,66,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7167 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7168 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 261 74 84 33 96 152 280), lower := (rows 35 134 261 74 84 33 96 128 256), losses := [] }

theorem u7168 : Upper (D 6) (R 6) [34,132,257,66,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7169 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 35 134 261 74 84 48 65 168 296), lower := (rows 35 134 261 74 84 48 65 128 256), losses := [] }

theorem u7169 : Upper (D 6) (R 6) [34,132,257,66,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7169 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7170 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 134 261 74 84 48 72 161 289), lower := (rows 35 134 261 74 84 48 72 128 256), losses := [] }

theorem u7170 : Upper (D 6) (R 6) [34,132,257,66,68,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7170 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7171 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 120, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 134 261 74 84 48 96 137 265), lower := (rows 35 134 261 74 84 48 96 128 256), losses := [] }

theorem u7171 : Upper (D 6) (R 6) [34,132,257,66,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7171 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7172 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 112, targets := 6 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,1),(4,2)], upper := (rows 35 134 262 13 56 96 65 208 336), lower := (rows 35 134 262 13 56 96 65 128 256), losses := [] }

theorem u7172 : Upper (D 6) (R 6) [34,132,258,5,40,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7173 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 13 56 96 80 193 321), lower := (rows 35 134 262 13 56 96 80 128 256), losses := [] }

theorem u7173 : Upper (D 6) (R 6) [34,132,258,5,40,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7173 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7174 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 262 13 81 96 72 176 304), lower := (rows 35 134 262 13 81 96 72 128 256), losses := [] }

theorem u7174 : Upper (D 6) (R 6) [34,132,258,5,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7174 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7175 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 262 13 81 96 80 168 296), lower := (rows 35 134 262 13 81 96 80 128 256), losses := [] }

theorem u7175 : Upper (D 6) (R 6) [34,132,258,5,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7175 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7176 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 262 13 81 96 96 152 280), lower := (rows 35 134 262 13 81 96 96 128 256), losses := [] }

theorem u7176 : Upper (D 6) (R 6) [34,132,258,5,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7177 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 6 },{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 35 134 262 13 88 96 65 176 304), lower := (rows 35 134 262 13 88 96 65 128 256), losses := [] }

theorem u7177 : Upper (D 6) (R 6) [34,132,258,5,72,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7178 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 262 13 88 96 80 161 289), lower := (rows 35 134 262 13 88 96 80 128 256), losses := [] }

theorem u7178 : Upper (D 6) (R 6) [34,132,258,5,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7178 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7179 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 112, targets := 6 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,1),(4,2)], upper := (rows 35 134 262 13 88 96 96 145 273), lower := (rows 35 134 262 13 88 96 96 128 256), losses := [] }

theorem u7179 : Upper (D 6) (R 6) [34,132,258,5,72,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7180 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 390, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 262 25 28 96 65 224 352), lower := (rows 35 134 262 25 28 96 65 128 256), losses := [] }

theorem u7180 : Upper (D 6) (R 6) [34,132,258,17,12,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7181 : Route 9 := (fun mask => (mask,id))

def c7181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7181 : Upper (D 6) (R 6) [34,132,258,17,12,64,32] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,12,64,32] 13 (by decide) (choices 1) [1,64] r7181 c7181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u541
  · exact u542

def b7182 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 134 262 25 52 96 65 200 328), lower := (rows 35 134 262 25 52 96 65 128 256), losses := [] }

theorem u7182 : Upper (D 6) (R 6) [34,132,258,17,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7183 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 25 52 96 72 193 321), lower := (rows 35 134 262 25 52 96 72 128 256), losses := [] }

theorem u7183 : Upper (D 6) (R 6) [34,132,258,17,36,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7183 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7184 : Route 9 := (fun mask => (mask,id))

def c7184 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7184 : Upper (D 6) (R 6) [34,132,258,17,68,8,1] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,68,8,1] 13 (by decide) (choices 1) [32,64] r7184 c7184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u543
  · exact u544

def r7185 : Route 9 := (fun mask => (mask,id))

def c7185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7185 : Upper (D 6) (R 6) [34,132,258,17,68,8,32] 13 := by
  apply FastRouting.sound _ _ [34,132,258,17,68,8,32] 13 (by decide) (choices 1) [1,64] r7185 c7185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u545
  · exact u546

def b7186 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 262 25 84 96 65 168 296), lower := (rows 35 134 262 25 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 112 64 136 264), good := (rows 34 134 262 446 116 96 96 128 256) }] }

theorem u7186 : Upper (D 6) (R 6) [34,132,258,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7187 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 262 25 84 96 72 161 289), lower := (rows 35 134 262 25 84 96 72 128 256), losses := [] }

theorem u7187 : Upper (D 6) (R 6) [34,132,258,17,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7187 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7188 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 262 25 84 96 96 137 265), lower := (rows 35 134 262 25 84 96 96 128 256), losses := [] }

theorem u7188 : Upper (D 6) (R 6) [34,132,258,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7189 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 134 262 28 81 96 65 168 296), lower := (rows 35 134 262 28 81 96 65 128 256), losses := [] }

theorem u7189 : Upper (D 6) (R 6) [34,132,258,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7190 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 262 28 81 96 72 161 289), lower := (rows 35 134 262 28 81 96 72 128 256), losses := [] }

theorem u7190 : Upper (D 6) (R 6) [34,132,258,20,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7190 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7191 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 262 28 81 96 96 137 265), lower := (rows 35 134 262 28 81 96 96 128 256), losses := [] }

theorem u7191 : Upper (D 6) (R 6) [34,132,258,20,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7192 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 134 262 44 81 48 65 200 328), lower := (rows 35 134 262 44 81 48 65 128 256), losses := [] }

theorem u7192 : Upper (D 6) (R 6) [34,132,258,36,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7192 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7193 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 35 134 262 44 81 48 72 193 321), lower := (rows 35 134 262 44 81 48 72 128 256), losses := [] }

theorem u7193 : Upper (D 6) (R 6) [34,132,258,36,65,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7193 [(5,4),(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7194 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 134 262 44 81 96 65 152 280), lower := (rows 35 134 262 44 81 96 65 128 256), losses := [] }

theorem u7194 : Upper (D 6) (R 6) [34,132,258,36,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7195 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 390, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 35 134 262 44 81 96 72 145 273), lower := (rows 35 134 262 44 81 96 72 128 256), losses := [] }

theorem u7195 : Upper (D 6) (R 6) [34,132,258,36,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7195 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7196 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 262 44 81 96 80 137 265), lower := (rows 35 134 262 44 81 96 80 128 256), losses := [] }

theorem u7196 : Upper (D 6) (R 6) [34,132,258,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7196 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7197 : Route 9 := (fun mask => (mask,id))

def c7197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7197 : Upper (D 6) (R 6) [34,132,258,36,72,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,258,36,72,64,1] 13 (by decide) (choices 1) [1,16] r7197 c7197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u547
  · exact u548

def b7198 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 134 262 44 88 96 80 129 257), lower := (rows 35 134 262 44 88 96 80 128 256), losses := [] }

theorem u7198 : Upper (D 6) (R 6) [34,132,258,36,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7198 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7199 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 134 262 73 84 40 65 176 304), lower := (rows 35 134 262 73 84 40 65 128 256), losses := [] }

theorem u7199 : Upper (D 6) (R 6) [34,132,258,65,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7199 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7199
end Delivery.IrregularNine14.P06
