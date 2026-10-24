import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6060 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 259 69 140 176 96 80 138 266), lower := (rows 35 259 69 140 176 96 80 128 256), losses := [] }

theorem u6060 : Upper (D 7) (R 7) [34,257,65,132,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6060 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6061 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 69 140 208 40 66 176 304), lower := (rows 35 259 69 140 208 40 66 128 256), losses := [] }

theorem u6061 : Upper (D 7) (R 7) [34,257,65,132,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6061 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6062 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 69 140 208 40 80 162 290), lower := (rows 35 259 69 140 208 40 80 128 256), losses := [] }

theorem u6062 : Upper (D 7) (R 7) [34,257,65,132,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6062 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6063 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 140 208 40 96 146 274), lower := (rows 35 259 69 140 208 40 96 128 256), losses := [] }

theorem u6063 : Upper (D 7) (R 7) [34,257,65,132,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6063 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6064 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 69 140 208 48 66 168 296), lower := (rows 35 259 69 140 208 48 66 128 256), losses := [] }

theorem u6064 : Upper (D 7) (R 7) [34,257,65,132,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6065 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 259 69 140 208 48 72 162 290), lower := (rows 35 259 69 140 208 48 72 128 256), losses := [] }

theorem u6065 : Upper (D 7) (R 7) [34,257,65,132,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6065 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6066 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 259 69 140 208 48 96 138 266), lower := (rows 35 259 69 140 208 48 96 128 256), losses := [] }

theorem u6066 : Upper (D 7) (R 7) [34,257,65,132,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6066 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6067 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 69 168 208 36 66 152 280), lower := (rows 35 259 69 168 208 36 66 128 256), losses := [] }

theorem u6067 : Upper (D 7) (R 7) [34,257,65,160,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6067 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6068 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 259 69 168 208 36 72 146 274), lower := (rows 35 259 69 168 208 36 72 128 256), losses := [] }

theorem u6068 : Upper (D 7) (R 7) [34,257,65,160,192,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6068 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6069 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 69 168 208 36 80 138 266), lower := (rows 35 259 69 168 208 36 80 128 256), losses := [] }

theorem u6069 : Upper (D 7) (R 7) [34,257,65,160,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6069 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6070 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 88 148 40 65 160 416), lower := (rows 35 259 70 88 148 40 65 128 256), losses := [] }

theorem u6070 : Upper (D 7) (R 7) [34,257,66,80,132,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6070 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6071 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 104, targets := 131 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 35 259 70 88 148 40 96 129 385), lower := (rows 35 259 70 88 148 40 96 128 256), losses := [] }

theorem u6071 : Upper (D 7) (R 7) [34,257,66,80,132,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6071 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6072 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 70 88 148 40 192 161 289), lower := (rows 35 259 70 88 148 40 192 128 256), losses := [] }

theorem u6072 : Upper (D 7) (R 7) [34,257,66,80,132,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6072 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6073 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 70 88 148 160 65 168 296), lower := (rows 35 259 70 88 148 160 65 128 256), losses := [] }

theorem u6073 : Upper (D 7) (R 7) [34,257,66,80,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6074 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 70 88 148 160 72 161 289), lower := (rows 35 259 70 88 148 160 72 128 256), losses := [] }

theorem u6074 : Upper (D 7) (R 7) [34,257,66,80,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6074 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6075 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 419, targets := 64 },{ cop := 4, region := 104, targets := 3 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 35 259 70 88 148 160 96 137 265), lower := (rows 35 259 70 88 148 160 96 128 256), losses := [] }

theorem u6075 : Upper (D 7) (R 7) [34,257,66,80,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6076 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 88 176 40 65 132 388), lower := (rows 35 259 70 88 176 40 65 128 256), losses := [] }

theorem u6076 : Upper (D 7) (R 7) [34,257,66,80,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6076 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6077 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 70 88 176 40 68 129 385), lower := (rows 35 259 70 88 176 40 68 128 256), losses := [] }

theorem u6077 : Upper (D 7) (R 7) [34,257,66,80,160,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6077 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6078 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 88 176 40 192 133 261), lower := (rows 35 259 70 88 176 40 192 128 256), losses := [] }

theorem u6078 : Upper (D 7) (R 7) [34,257,66,80,160,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6078 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6079 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 70 104 148 160 65 152 280), lower := (rows 35 259 70 104 148 160 65 128 256), losses := [] }

theorem u6079 : Upper (D 7) (R 7) [34,257,66,96,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6080 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 70 104 148 160 72 145 273), lower := (rows 35 259 70 104 148 160 72 128 256), losses := [] }

theorem u6080 : Upper (D 7) (R 7) [34,257,66,96,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6080 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6081 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 70 104 148 160 80 137 265), lower := (rows 35 259 70 104 148 160 80 128 256), losses := [] }

theorem u6081 : Upper (D 7) (R 7) [34,257,66,96,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6081 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6082 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 104 152 48 65 132 388), lower := (rows 35 259 70 104 152 48 65 128 256), losses := [] }

theorem u6082 : Upper (D 7) (R 7) [34,257,66,96,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6082 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6083 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 70 104 152 48 68 129 385), lower := (rows 35 259 70 104 152 48 68 128 256), losses := [] }

theorem u6083 : Upper (D 7) (R 7) [34,257,66,96,136,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6083 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6084 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 104 152 48 192 133 261), lower := (rows 35 259 70 104 152 48 192 128 256), losses := [] }

theorem u6084 : Upper (D 7) (R 7) [34,257,66,96,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6084 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6085 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 70 104 152 160 65 148 276), lower := (rows 35 259 70 104 152 160 65 128 256), losses := [] }

theorem u6085 : Upper (D 7) (R 7) [34,257,66,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6086 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 68, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 35 259 70 104 152 160 68 145 273), lower := (rows 35 259 70 104 152 160 68 128 256), losses := [] }

theorem u6086 : Upper (D 7) (R 7) [34,257,66,96,136,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6086 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6087 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 104 152 160 80 133 261), lower := (rows 35 259 70 104 152 160 80 128 256), losses := [] }

theorem u6087 : Upper (D 7) (R 7) [34,257,66,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6087 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6088 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 70 140 176 96 65 152 280), lower := (rows 35 259 70 140 176 96 65 128 256), losses := [] }

theorem u6088 : Upper (D 7) (R 7) [34,257,66,132,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6089 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 70 140 176 96 72 145 273), lower := (rows 35 259 70 140 176 96 72 128 256), losses := [] }

theorem u6089 : Upper (D 7) (R 7) [34,257,66,132,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6089 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6090 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(4,0),(4,1)], upper := (rows 35 259 70 140 176 96 80 137 265), lower := (rows 35 259 70 140 176 96 80 128 256), losses := [] }

theorem u6090 : Upper (D 7) (R 7) [34,257,66,132,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6090 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6091 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 140 208 40 65 176 304), lower := (rows 35 259 70 140 208 40 65 128 256), losses := [] }

theorem u6091 : Upper (D 7) (R 7) [34,257,66,132,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6091 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6092 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 259 70 140 208 40 80 161 289), lower := (rows 35 259 70 140 208 40 80 128 256), losses := [] }

theorem u6092 : Upper (D 7) (R 7) [34,257,66,132,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6092 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6093 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 35 259 70 140 208 40 96 145 273), lower := (rows 35 259 70 140 208 40 96 128 256), losses := [] }

theorem u6093 : Upper (D 7) (R 7) [34,257,66,132,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6093 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6094 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 70 140 208 48 65 168 296), lower := (rows 35 259 70 140 208 48 65 128 256), losses := [] }

theorem u6094 : Upper (D 7) (R 7) [34,257,66,132,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6094 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6095 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 259 70 140 208 48 72 161 289), lower := (rows 35 259 70 140 208 48 72 128 256), losses := [] }

theorem u6095 : Upper (D 7) (R 7) [34,257,66,132,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6095 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6096 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 112, targets := 3 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 35 259 70 140 208 48 96 137 265), lower := (rows 35 259 70 140 208 48 96 128 256), losses := [] }

theorem u6096 : Upper (D 7) (R 7) [34,257,66,132,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6096 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6097 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 13 26 81 160 96 192 448), lower := (rows 35 262 13 26 81 160 96 128 256), losses := [] }

theorem u6097 : Upper (D 7) (R 7) [34,260,9,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6098 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,1)], upper := (rows 35 262 13 26 81 160 192 224 352), lower := (rows 35 262 13 26 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 224 128 256), good := (rows 95 262 29 30 93 192 192 192 256) }] }

theorem u6098 : Upper (D 7) (R 7) [34,260,9,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6099 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 6, region := 176, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 262 13 26 112 160 65 192 448), lower := (rows 35 262 13 26 112 160 65 128 256), losses := [] }

theorem u6099 : Upper (D 7) (R 7) [34,260,9,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6100 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 13 26 112 160 192 193 321), lower := (rows 35 262 13 26 112 160 192 128 256), losses := [] }

theorem u6100 : Upper (D 7) (R 7) [34,260,9,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6101 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 13 56 82 160 65 192 448), lower := (rows 35 262 13 56 82 160 65 128 256), losses := [] }

theorem u6101 : Upper (D 7) (R 7) [34,260,9,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6102 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 262 13 56 82 160 192 193 321), lower := (rows 35 262 13 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 25 17 224 224 128 256), good := (rows 122 262 28 120 122 224 224 224 256) }] }

theorem u6102 : Upper (D 7) (R 7) [34,260,9,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6103 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 262 13 74 81 160 80 160 416), lower := (rows 35 262 13 74 81 160 80 128 256), losses := [] }

theorem u6103 : Upper (D 7) (R 7) [34,260,9,66,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6103 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6104 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 13 74 81 160 96 144 400), lower := (rows 35 262 13 74 81 160 96 128 256), losses := [] }

theorem u6104 : Upper (D 7) (R 7) [34,260,9,66,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6105 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(2,5),(3,0),(3,5),(4,1)], upper := (rows 35 262 13 74 81 160 192 176 304), lower := (rows 35 262 13 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 16 240 240 144 272), good := (rows 106 262 12 106 504 224 224 224 256) },{ target := 5, region := (rows 1 2 21 9 17 0 224 128 256), good := (rows 95 262 29 74 93 192 192 192 256) }] }

theorem u6105 : Upper (D 7) (R 7) [34,260,9,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6106 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 76, targets := 32 }], pairs := [(2,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 13 74 112 160 65 144 400), lower := (rows 35 262 13 74 112 160 65 128 256), losses := [] }

theorem u6106 : Upper (D 7) (R 7) [34,260,9,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6107 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 13 74 112 160 80 129 385), lower := (rows 35 262 13 74 112 160 80 128 256), losses := [] }

theorem u6107 : Upper (D 7) (R 7) [34,260,9,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6107 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6108 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 13 74 112 160 192 145 273), lower := (rows 35 262 13 74 112 160 192 128 256), losses := [] }

theorem u6108 : Upper (D 7) (R 7) [34,260,9,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6109 : Route 9 := (fun mask => (mask,id))

def c6109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u6109 : Upper (D 7) (R 7) [34,260,9,66,129,128,16] 13 := by
  apply FastRouting.sound _ _ [34,260,9,66,129,128,16] 13 (by decide) (choices 1) [32,64] r6109 c6109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u460
  · exact u461

def b6110 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,7),(3,0),(3,7),(4,1)], upper := (rows 35 262 13 74 145 160 96 208 336), lower := (rows 35 262 13 74 145 160 96 128 256), losses := [] }

theorem u6110 : Upper (D 7) (R 7) [34,260,9,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6111 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 262 13 74 208 48 65 160 416), lower := (rows 35 262 13 74 208 48 65 128 256), losses := [] }

theorem u6111 : Upper (D 7) (R 7) [34,260,9,66,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6111 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6112 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 386, targets := 32 }], pairs := [(1,5),(2,7),(3,7)], upper := (rows 35 262 13 74 208 48 96 129 385), lower := (rows 35 262 13 74 208 48 96 128 256), losses := [] }

theorem u6112 : Upper (D 7) (R 7) [34,260,9,66,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6113 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 13 74 208 48 192 161 289), lower := (rows 35 262 13 74 208 48 192 128 256), losses := [] }

theorem u6113 : Upper (D 7) (R 7) [34,260,9,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6113 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6114 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 262 13 74 208 160 65 176 304), lower := (rows 35 262 13 74 208 160 65 128 256), losses := [] }

theorem u6114 : Upper (D 7) (R 7) [34,260,9,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6115 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 13 74 208 160 80 161 289), lower := (rows 35 262 13 74 208 160 80 128 256), losses := [] }

theorem u6115 : Upper (D 7) (R 7) [34,260,9,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6115 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6116 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 5, region := 80, targets := 3 }], pairs := [(2,7),(3,7),(4,0),(4,1)], upper := (rows 35 262 13 74 208 160 96 145 273), lower := (rows 35 262 13 74 208 160 96 128 256), losses := [] }

theorem u6116 : Upper (D 7) (R 7) [34,260,9,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6117 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 35 262 13 88 146 96 65 160 416), lower := (rows 35 262 13 88 146 96 65 128 256), losses := [] }

theorem u6117 : Upper (D 7) (R 7) [34,260,9,80,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6118 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 35 262 13 88 146 96 96 129 385), lower := (rows 35 262 13 88 146 96 96 128 256), losses := [] }

theorem u6118 : Upper (D 7) (R 7) [34,260,9,80,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6119 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 13 88 146 96 192 161 289), lower := (rows 35 262 13 88 146 96 192 128 256), losses := [] }

theorem u6119 : Upper (D 7) (R 7) [34,260,9,80,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6119
end Delivery.IrregularNine14.P07
