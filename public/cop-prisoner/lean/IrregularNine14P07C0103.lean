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

def b6180 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 262 69 25 82 160 72 160 416), lower := (rows 35 262 69 25 82 160 72 128 256), losses := [] }

theorem u6180 : Upper (D 7) (R 7) [34,260,65,17,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6180 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6181 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 69 25 82 160 96 136 392), lower := (rows 35 262 69 25 82 160 96 128 256), losses := [] }

theorem u6181 : Upper (D 7) (R 7) [34,260,65,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6182 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 169, targets := 64 },{ cop := 3, region := 228, targets := 2 }], pairs := [(0,6),(2,1),(3,6),(4,0)], upper := (rows 35 262 69 25 82 160 192 168 296), lower := (rows 35 262 69 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 232 232 136 264), good := (rows 114 262 116 504 114 224 224 224 256) }] }

theorem u6182 : Upper (D 7) (R 7) [34,260,65,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6183 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,7),(3,1),(3,7),(4,7)], upper := (rows 35 262 69 25 112 160 66 136 392), lower := (rows 35 262 69 25 112 160 66 128 256), losses := [] }

theorem u6183 : Upper (D 7) (R 7) [34,260,65,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6184 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 69 25 112 160 72 130 386), lower := (rows 35 262 69 25 112 160 72 128 256), losses := [] }

theorem u6184 : Upper (D 7) (R 7) [34,260,65,17,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6184 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6185 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 69 25 112 160 192 138 266), lower := (rows 35 262 69 25 112 160 192 128 256), losses := [] }

theorem u6185 : Upper (D 7) (R 7) [34,260,65,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6186 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 3, region := 68, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 35 262 69 25 146 160 72 224 352), lower := (rows 35 262 69 25 146 160 72 128 256), losses := [] }

theorem u6186 : Upper (D 7) (R 7) [34,260,65,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6186 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6187 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 69 25 146 160 96 200 328), lower := (rows 35 262 69 25 146 160 96 128 256), losses := [] }

theorem u6187 : Upper (D 7) (R 7) [34,260,65,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6188 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,5),(2,7),(3,1),(4,1)], upper := (rows 35 262 69 25 208 160 66 168 296), lower := (rows 35 262 69 25 208 160 66 128 256), losses := [] }

theorem u6188 : Upper (D 7) (R 7) [34,260,65,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6189 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 35 262 69 25 208 160 72 162 290), lower := (rows 35 262 69 25 208 160 72 128 256), losses := [] }

theorem u6189 : Upper (D 7) (R 7) [34,260,65,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6189 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6190 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 69 25 208 160 96 138 266), lower := (rows 35 262 69 25 208 160 96 128 256), losses := [] }

theorem u6190 : Upper (D 7) (R 7) [34,260,65,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6191 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 262 69 26 88 160 65 160 416), lower := (rows 35 262 69 26 88 160 65 128 256), losses := [] }

theorem u6191 : Upper (D 7) (R 7) [34,260,65,18,72,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6192 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 386, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 69 26 88 160 96 129 385), lower := (rows 35 262 69 26 88 160 96 128 256), losses := [] }

theorem u6192 : Upper (D 7) (R 7) [34,260,65,18,72,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6193 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(3,0)], upper := (rows 35 262 69 26 88 160 192 161 289), lower := (rows 35 262 69 26 88 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 21 224 224 128 256), good := (rows 122 286 124 26 120 224 224 224 256) }] }

theorem u6193 : Upper (D 7) (R 7) [34,260,65,18,72,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6194 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 69 26 112 160 65 136 392), lower := (rows 35 262 69 26 112 160 65 128 256), losses := [] }

theorem u6194 : Upper (D 7) (R 7) [34,260,65,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6195 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 69 26 112 160 72 129 385), lower := (rows 35 262 69 26 112 160 72 128 256), losses := [] }

theorem u6195 : Upper (D 7) (R 7) [34,260,65,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6195 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6196 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 69 26 112 160 192 137 265), lower := (rows 35 262 69 26 112 160 192 128 256), losses := [] }

theorem u6196 : Upper (D 7) (R 7) [34,260,65,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6197 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 418, targets := 1 },{ cop := 2, region := 176, targets := 2 }], pairs := [(0,6),(1,0),(4,1)], upper := (rows 35 262 69 26 145 160 72 224 352), lower := (rows 35 262 69 26 145 160 72 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 176 0 128 256), good := (rows 35 262 5 59 177 160 9 160 256) }] }

theorem u6197 : Upper (D 7) (R 7) [34,260,65,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6197 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6198 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 69 26 145 160 96 200 328), lower := (rows 35 262 69 26 145 160 96 128 256), losses := [] }

theorem u6198 : Upper (D 7) (R 7) [34,260,65,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6199 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 162 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 69 26 208 160 65 168 296), lower := (rows 35 262 69 26 208 160 65 128 256), losses := [] }

theorem u6199 : Upper (D 7) (R 7) [34,260,65,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6200 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 2, region := 176, targets := 2 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 35 262 69 26 208 160 72 161 289), lower := (rows 35 262 69 26 208 160 72 128 256), losses := [] }

theorem u6200 : Upper (D 7) (R 7) [34,260,65,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6200 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6201 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 69 26 208 160 96 137 265), lower := (rows 35 262 69 26 208 160 96 128 256), losses := [] }

theorem u6201 : Upper (D 7) (R 7) [34,260,65,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6202 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 69 56 82 160 65 136 392), lower := (rows 35 262 69 56 82 160 65 128 256), losses := [] }

theorem u6202 : Upper (D 7) (R 7) [34,260,65,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6203 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 69 56 82 160 72 129 385), lower := (rows 35 262 69 56 82 160 72 128 256), losses := [] }

theorem u6203 : Upper (D 7) (R 7) [34,260,65,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6203 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6204 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(3,0),(3,6),(4,0)], upper := (rows 35 262 69 56 82 160 192 137 265), lower := (rows 35 262 69 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 29 17 224 224 128 256), good := (rows 122 270 124 120 122 224 224 224 256) }] }

theorem u6204 : Upper (D 7) (R 7) [34,260,65,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6205 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 262 69 74 145 160 72 176 304), lower := (rows 35 262 69 74 145 160 72 128 256), losses := [] }

theorem u6205 : Upper (D 7) (R 7) [34,260,65,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6205 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6206 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 426, targets := 1 },{ cop := 3, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(3,0)], upper := (rows 35 262 69 74 145 160 80 168 296), lower := (rows 35 262 69 74 145 160 80 128 256), losses := [] }

theorem u6206 : Upper (D 7) (R 7) [34,260,65,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6206 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6207 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 262 69 74 145 160 96 152 280), lower := (rows 35 262 69 74 145 160 96 128 256), losses := [] }

theorem u6207 : Upper (D 7) (R 7) [34,260,65,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6208 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 262 69 74 152 160 65 176 304), lower := (rows 35 262 69 74 152 160 65 128 256), losses := [] }

theorem u6208 : Upper (D 7) (R 7) [34,260,65,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6209 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 69 74 152 160 80 161 289), lower := (rows 35 262 69 74 152 160 80 128 256), losses := [] }

theorem u6209 : Upper (D 7) (R 7) [34,260,65,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6209 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6210 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 262 69 74 152 160 96 145 273), lower := (rows 35 262 69 74 152 160 96 128 256), losses := [] }

theorem u6210 : Upper (D 7) (R 7) [34,260,65,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6211 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,5),(2,7),(3,1),(4,1)], upper := (rows 35 262 69 88 145 160 66 168 296), lower := (rows 35 262 69 88 145 160 66 128 256), losses := [] }

theorem u6211 : Upper (D 7) (R 7) [34,260,65,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6212 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 262 69 88 145 160 72 162 290), lower := (rows 35 262 69 88 145 160 72 128 256), losses := [] }

theorem u6212 : Upper (D 7) (R 7) [34,260,65,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6212 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6213 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 69 88 145 160 96 138 266), lower := (rows 35 262 69 88 145 160 96 128 256), losses := [] }

theorem u6213 : Upper (D 7) (R 7) [34,260,65,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6214 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 162 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 35 262 69 88 146 160 65 168 296), lower := (rows 35 262 69 88 146 160 65 128 256), losses := [] }

theorem u6214 : Upper (D 7) (R 7) [34,260,65,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6215 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 69 88 146 160 72 161 289), lower := (rows 35 262 69 88 146 160 72 128 256), losses := [] }

theorem u6215 : Upper (D 7) (R 7) [34,260,65,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6215 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6216 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,5),(2,1),(3,5),(4,5)], upper := (rows 35 262 69 88 146 160 96 137 265), lower := (rows 35 262 69 88 146 160 96 128 256), losses := [] }

theorem u6216 : Upper (D 7) (R 7) [34,260,65,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6217 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,7),(3,1),(3,7)], upper := (rows 35 262 69 104 145 48 66 136 392), lower := (rows 35 262 69 104 145 48 66 128 256), losses := [] }

theorem u6217 : Upper (D 7) (R 7) [34,260,65,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6217 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6218 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 262 69 104 145 48 72 130 386), lower := (rows 35 262 69 104 145 48 72 128 256), losses := [] }

theorem u6218 : Upper (D 7) (R 7) [34,260,65,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6218 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6219 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 69 104 145 48 192 138 266), lower := (rows 35 262 69 104 145 48 192 128 256), losses := [] }

theorem u6219 : Upper (D 7) (R 7) [34,260,65,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6219 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6220 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,7),(3,1),(3,7),(4,1)], upper := (rows 35 262 69 104 145 160 66 152 280), lower := (rows 35 262 69 104 145 160 66 128 256), losses := [] }

theorem u6220 : Upper (D 7) (R 7) [34,260,65,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6221 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 69 104 145 160 72 146 274), lower := (rows 35 262 69 104 145 160 72 128 256), losses := [] }

theorem u6221 : Upper (D 7) (R 7) [34,260,65,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6221 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6222 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 69 104 145 160 80 138 266), lower := (rows 35 262 69 104 145 160 80 128 256), losses := [] }

theorem u6222 : Upper (D 7) (R 7) [34,260,65,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6222 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6223 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 69 104 146 160 65 152 280), lower := (rows 35 262 69 104 146 160 65 128 256), losses := [] }

theorem u6223 : Upper (D 7) (R 7) [34,260,65,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6224 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 69 104 146 160 72 145 273), lower := (rows 35 262 69 104 146 160 72 128 256), losses := [] }

theorem u6224 : Upper (D 7) (R 7) [34,260,65,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6224 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6225 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 69 104 146 160 80 137 265), lower := (rows 35 262 69 104 146 160 80 128 256), losses := [] }

theorem u6225 : Upper (D 7) (R 7) [34,260,65,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6225 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6226 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 69 104 152 160 65 146 274), lower := (rows 35 262 69 104 152 160 65 128 256), losses := [] }

theorem u6226 : Upper (D 7) (R 7) [34,260,65,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6227 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,7),(3,1),(3,7),(4,1)], upper := (rows 35 262 69 104 152 160 66 145 273), lower := (rows 35 262 69 104 152 160 66 128 256), losses := [] }

theorem u6227 : Upper (D 7) (R 7) [34,260,65,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6228 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 262 69 104 152 160 80 131 259), lower := (rows 35 262 69 104 152 160 80 128 256), losses := [] }

theorem u6228 : Upper (D 7) (R 7) [34,260,65,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6228 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6229 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 68, targets := 160 },{ cop := 2, region := 184, targets := 2 }], pairs := [(2,5),(2,7),(3,1)], upper := (rows 35 262 69 137 208 40 66 176 304), lower := (rows 35 262 69 137 208 40 66 128 256), losses := [] }

theorem u6229 : Upper (D 7) (R 7) [34,260,65,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6229 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6230 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 262 69 137 208 40 80 162 290), lower := (rows 35 262 69 137 208 40 80 128 256), losses := [] }

theorem u6230 : Upper (D 7) (R 7) [34,260,65,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6230 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6231 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 262 69 137 208 40 96 146 274), lower := (rows 35 262 69 137 208 40 96 128 256), losses := [] }

theorem u6231 : Upper (D 7) (R 7) [34,260,65,129,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6231 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6232 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(3,6)], upper := (rows 35 262 69 137 208 48 66 168 296), lower := (rows 35 262 69 137 208 48 66 128 256), losses := [] }

theorem u6232 : Upper (D 7) (R 7) [34,260,65,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6233 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 262 69 137 208 48 72 162 290), lower := (rows 35 262 69 137 208 48 72 128 256), losses := [] }

theorem u6233 : Upper (D 7) (R 7) [34,260,65,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6233 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6234 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 262 69 137 208 48 96 138 266), lower := (rows 35 262 69 137 208 48 96 128 256), losses := [] }

theorem u6234 : Upper (D 7) (R 7) [34,260,65,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6234 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6235 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 35 262 69 138 208 48 65 168 296), lower := (rows 35 262 69 138 208 48 65 128 256), losses := [] }

theorem u6235 : Upper (D 7) (R 7) [34,260,65,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6235 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6236 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 262 69 138 208 48 72 161 289), lower := (rows 35 262 69 138 208 48 72 128 256), losses := [] }

theorem u6236 : Upper (D 7) (R 7) [34,260,65,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6236 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6237 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 262 69 138 208 48 96 137 265), lower := (rows 35 262 69 138 208 48 96 128 256), losses := [] }

theorem u6237 : Upper (D 7) (R 7) [34,260,65,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6237 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6238 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 35 262 70 25 208 40 65 160 416), lower := (rows 35 262 70 25 208 40 65 128 256), losses := [] }

theorem u6238 : Upper (D 7) (R 7) [34,260,66,17,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6238 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6239 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,1),(4,1)], upper := (rows 35 262 70 25 208 40 96 129 385), lower := (rows 35 262 70 25 208 40 96 128 256), losses := [] }

theorem u6239 : Upper (D 7) (R 7) [34,260,66,17,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6239 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6239
end Delivery.IrregularNine14.P07
