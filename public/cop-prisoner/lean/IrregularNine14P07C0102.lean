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

def b6120 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 35 262 13 88 146 160 65 224 352), lower := (rows 35 262 13 88 146 160 65 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 252 64 200 328), good := (rows 34 310 446 504 178 160 480 160 256) },{ target := 6, region := (rows 17 2 12 8 16 176 0 128 256), good := (rows 35 262 13 61 179 160 1 160 256) }] }

theorem u6120 : Upper (D 7) (R 7) [34,260,9,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6121 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 35 262 13 88 146 160 96 193 321), lower := (rows 35 262 13 88 146 160 96 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 176 0 128 256), good := (rows 35 262 13 61 179 160 32 160 256) }] }

theorem u6121 : Upper (D 7) (R 7) [34,260,9,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6122 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 386, targets := 65 },{ cop := 0, region := 144, targets := 1 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 35 262 13 88 176 96 65 130 386), lower := (rows 35 262 13 88 176 96 65 128 256), losses := [] }

theorem u6122 : Upper (D 7) (R 7) [34,260,9,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6123 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 97, targets := 128 },{ cop := 2, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(4,1),(4,6)], upper := (rows 35 262 13 88 176 96 66 129 385), lower := (rows 35 262 13 88 176 96 66 128 256), losses := [] }

theorem u6123 : Upper (D 7) (R 7) [34,260,9,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6124 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 262 13 88 176 96 192 131 259), lower := (rows 35 262 13 88 176 96 192 128 256), losses := [] }

theorem u6124 : Upper (D 7) (R 7) [34,260,9,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6125 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 13 104 81 160 66 144 400), lower := (rows 35 262 13 104 81 160 66 128 256), losses := [] }

theorem u6125 : Upper (D 7) (R 7) [34,260,9,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6126 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 13 104 81 160 80 130 386), lower := (rows 35 262 13 104 81 160 80 128 256), losses := [] }

theorem u6126 : Upper (D 7) (R 7) [34,260,9,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6126 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6127 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 262 13 104 81 160 192 146 274), lower := (rows 35 262 13 104 81 160 192 128 256), losses := [] }

theorem u6127 : Upper (D 7) (R 7) [34,260,9,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6128 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(2,7),(3,7),(4,7)], upper := (rows 35 262 13 104 82 160 65 144 400), lower := (rows 35 262 13 104 82 160 65 128 256), losses := [] }

theorem u6128 : Upper (D 7) (R 7) [34,260,9,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6129 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 13 104 82 160 80 129 385), lower := (rows 35 262 13 104 82 160 80 128 256), losses := [] }

theorem u6129 : Upper (D 7) (R 7) [34,260,9,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6129 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6130 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 262 13 104 82 160 192 145 273), lower := (rows 35 262 13 104 82 160 192 128 256), losses := [] }

theorem u6130 : Upper (D 7) (R 7) [34,260,9,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6131 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,5)], upper := (rows 35 262 13 104 145 160 66 208 336), lower := (rows 35 262 13 104 145 160 66 128 256), losses := [] }

theorem u6131 : Upper (D 7) (R 7) [34,260,9,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6132 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 13 104 145 160 80 194 322), lower := (rows 35 262 13 104 145 160 80 128 256), losses := [] }

theorem u6132 : Upper (D 7) (R 7) [34,260,9,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6132 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6133 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 13 104 146 160 65 208 336), lower := (rows 35 262 13 104 146 160 65 128 256), losses := [] }

theorem u6133 : Upper (D 7) (R 7) [34,260,9,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6134 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 13 104 146 160 80 193 321), lower := (rows 35 262 13 104 146 160 80 128 256), losses := [] }

theorem u6134 : Upper (D 7) (R 7) [34,260,9,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6134 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6135 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 172, targets := 2 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(2,1),(3,1),(4,5),(4,7)], upper := (rows 35 262 13 200 81 160 66 176 304), lower := (rows 35 262 13 200 81 160 66 128 256), losses := [] }

theorem u6135 : Upper (D 7) (R 7) [34,260,9,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6136 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 35 262 13 200 81 160 80 162 290), lower := (rows 35 262 13 200 81 160 80 128 256), losses := [] }

theorem u6136 : Upper (D 7) (R 7) [34,260,9,192,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6136 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6137 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 5, region := 72, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(3,5)], upper := (rows 35 262 13 200 81 160 96 146 274), lower := (rows 35 262 13 200 81 160 96 128 256), losses := [] }

theorem u6137 : Upper (D 7) (R 7) [34,260,9,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6138 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 168, targets := 3 },{ cop := 0, region := 80, targets := 32 },{ cop := 0, region := 80, targets := 128 }], pairs := [(3,0),(3,1),(4,5),(4,7)], upper := (rows 35 262 13 200 82 160 65 176 304), lower := (rows 35 262 13 200 82 160 65 128 256), losses := [] }

theorem u6138 : Upper (D 7) (R 7) [34,260,9,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6139 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 35 262 13 200 82 160 80 161 289), lower := (rows 35 262 13 200 82 160 80 128 256), losses := [] }

theorem u6139 : Upper (D 7) (R 7) [34,260,9,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6139 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6140 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 72, targets := 3 },{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 128 }], pairs := [(3,0),(3,1),(4,0),(4,7)], upper := (rows 35 262 13 200 82 160 96 145 273), lower := (rows 35 262 13 200 82 160 96 128 256), losses := [] }

theorem u6140 : Upper (D 7) (R 7) [34,260,9,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6141 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 14 73 112 160 65 144 400), lower := (rows 35 262 14 73 112 160 65 128 256), losses := [] }

theorem u6141 : Upper (D 7) (R 7) [34,260,10,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6142 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 14 73 112 160 80 129 385), lower := (rows 35 262 14 73 112 160 80 128 256), losses := [] }

theorem u6142 : Upper (D 7) (R 7) [34,260,10,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6142 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6143 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 14 73 112 160 192 145 273), lower := (rows 35 262 14 73 112 160 192 128 256), losses := [] }

theorem u6143 : Upper (D 7) (R 7) [34,260,10,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6144 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 35 262 14 73 145 160 80 224 352), lower := (rows 35 262 14 73 145 160 80 128 256), losses := [] }

theorem u6144 : Upper (D 7) (R 7) [34,260,10,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6144 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6145 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 14 73 145 160 96 208 336), lower := (rows 35 262 14 73 145 160 96 128 256), losses := [] }

theorem u6145 : Upper (D 7) (R 7) [34,260,10,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6146 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 262 14 73 208 160 65 176 304), lower := (rows 35 262 14 73 208 160 65 128 256), losses := [] }

theorem u6146 : Upper (D 7) (R 7) [34,260,10,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6147 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 14 73 208 160 80 161 289), lower := (rows 35 262 14 73 208 160 80 128 256), losses := [] }

theorem u6147 : Upper (D 7) (R 7) [34,260,10,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6147 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6148 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 14 73 208 160 96 145 273), lower := (rows 35 262 14 73 208 160 96 128 256), losses := [] }

theorem u6148 : Upper (D 7) (R 7) [34,260,10,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6149 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 14 104 81 160 65 144 400), lower := (rows 35 262 14 104 81 160 65 128 256), losses := [] }

theorem u6149 : Upper (D 7) (R 7) [34,260,10,96,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6150 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 14 104 81 160 80 129 385), lower := (rows 35 262 14 104 81 160 80 128 256), losses := [] }

theorem u6150 : Upper (D 7) (R 7) [34,260,10,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6150 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6151 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 262 14 104 81 160 192 145 273), lower := (rows 35 262 14 104 81 160 192 128 256), losses := [] }

theorem u6151 : Upper (D 7) (R 7) [34,260,10,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6152 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,1),(3,7),(4,1)], upper := (rows 35 262 14 104 145 160 65 208 336), lower := (rows 35 262 14 104 145 160 65 128 256), losses := [] }

theorem u6152 : Upper (D 7) (R 7) [34,260,10,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6153 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 14 104 145 160 80 193 321), lower := (rows 35 262 14 104 145 160 80 128 256), losses := [] }

theorem u6153 : Upper (D 7) (R 7) [34,260,10,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6153 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6154 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 262 14 200 81 48 65 160 416), lower := (rows 35 262 14 200 81 48 65 128 256), losses := [] }

theorem u6154 : Upper (D 7) (R 7) [34,260,10,192,65,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6154 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6155 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 14 200 81 48 96 129 385), lower := (rows 35 262 14 200 81 48 96 128 256), losses := [] }

theorem u6155 : Upper (D 7) (R 7) [34,260,10,192,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6155 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6156 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 14 200 81 48 192 161 289), lower := (rows 35 262 14 200 81 48 192 128 256), losses := [] }

theorem u6156 : Upper (D 7) (R 7) [34,260,10,192,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6156 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6157 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 262 28 73 82 160 65 160 416), lower := (rows 35 262 28 73 82 160 65 128 256), losses := [] }

theorem u6157 : Upper (D 7) (R 7) [34,260,24,65,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6158 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 262 28 73 82 160 96 129 385), lower := (rows 35 262 28 73 82 160 96 128 256), losses := [] }

theorem u6158 : Upper (D 7) (R 7) [34,260,24,65,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6159 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(1,6),(2,0),(3,1)], upper := (rows 35 262 28 73 82 160 192 161 289), lower := (rows 35 262 28 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 224 224 128 256), good := (rows 114 262 28 124 114 224 224 224 256) }] }

theorem u6159 : Upper (D 7) (R 7) [34,260,24,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6160 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 28 73 112 160 65 130 386), lower := (rows 35 262 28 73 112 160 65 128 256), losses := [] }

theorem u6160 : Upper (D 7) (R 7) [34,260,24,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6161 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 262 28 73 112 160 66 129 385), lower := (rows 35 262 28 73 112 160 66 128 256), losses := [] }

theorem u6161 : Upper (D 7) (R 7) [34,260,24,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6162 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 28 73 112 160 192 131 259), lower := (rows 35 262 28 73 112 160 192 128 256), losses := [] }

theorem u6162 : Upper (D 7) (R 7) [34,260,24,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6163 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 35 262 28 73 146 160 65 224 352), lower := (rows 35 262 28 73 146 160 65 128 256), losses := [] }

theorem u6163 : Upper (D 7) (R 7) [34,260,24,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6164 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 262 28 73 146 160 96 193 321), lower := (rows 35 262 28 73 146 160 96 128 256), losses := [] }

theorem u6164 : Upper (D 7) (R 7) [34,260,24,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6165 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 35 262 28 73 208 160 65 162 290), lower := (rows 35 262 28 73 208 160 65 128 256), losses := [] }

theorem u6165 : Upper (D 7) (R 7) [34,260,24,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6166 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 180, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 35 262 28 73 208 160 66 161 289), lower := (rows 35 262 28 73 208 160 66 128 256), losses := [] }

theorem u6166 : Upper (D 7) (R 7) [34,260,24,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6167 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(4,5)], upper := (rows 35 262 28 73 208 160 96 131 259), lower := (rows 35 262 28 73 208 160 96 128 256), losses := [] }

theorem u6167 : Upper (D 7) (R 7) [34,260,24,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6168 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,5),(3,7),(4,5)], upper := (rows 35 262 44 73 145 160 66 208 336), lower := (rows 35 262 44 73 145 160 66 128 256), losses := [] }

theorem u6168 : Upper (D 7) (R 7) [34,260,40,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6169 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 262 44 73 145 160 80 194 322), lower := (rows 35 262 44 73 145 160 80 128 256), losses := [] }

theorem u6169 : Upper (D 7) (R 7) [34,260,40,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6169 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6170 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 44 73 208 160 65 146 274), lower := (rows 35 262 44 73 208 160 65 128 256), losses := [] }

theorem u6170 : Upper (D 7) (R 7) [34,260,40,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6171 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,5),(3,7),(4,5)], upper := (rows 35 262 44 73 208 160 66 145 273), lower := (rows 35 262 44 73 208 160 66 128 256), losses := [] }

theorem u6171 : Upper (D 7) (R 7) [34,260,40,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6172 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 44 73 208 160 80 131 259), lower := (rows 35 262 44 73 208 160 80 128 256), losses := [] }

theorem u6172 : Upper (D 7) (R 7) [34,260,40,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6172 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6173 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 262 44 74 81 160 65 144 400), lower := (rows 35 262 44 74 81 160 65 128 256), losses := [] }

theorem u6173 : Upper (D 7) (R 7) [34,260,40,66,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6174 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 262 44 74 81 160 80 129 385), lower := (rows 35 262 44 74 81 160 80 128 256), losses := [] }

theorem u6174 : Upper (D 7) (R 7) [34,260,40,66,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6174 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6175 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(2,0),(3,5),(4,1),(4,5)], upper := (rows 35 262 44 74 81 160 192 145 273), lower := (rows 35 262 44 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 29 9 16 224 224 128 256), good := (rows 110 262 108 110 124 224 224 224 256) }] }

theorem u6175 : Upper (D 7) (R 7) [34,260,40,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6176 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,5),(3,7),(4,5)], upper := (rows 35 262 44 74 145 160 65 208 336), lower := (rows 35 262 44 74 145 160 65 128 256), losses := [] }

theorem u6176 : Upper (D 7) (R 7) [34,260,40,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6177 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 262 44 74 145 160 80 193 321), lower := (rows 35 262 44 74 145 160 80 128 256), losses := [] }

theorem u6177 : Upper (D 7) (R 7) [34,260,40,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6177 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6178 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,5),(3,7),(4,5)], upper := (rows 35 262 44 74 208 160 65 145 273), lower := (rows 35 262 44 74 208 160 65 128 256), losses := [] }

theorem u6178 : Upper (D 7) (R 7) [34,260,40,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6179 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 44 74 208 160 80 129 257), lower := (rows 35 262 44 74 208 160 80 128 256), losses := [] }

theorem u6179 : Upper (D 7) (R 7) [34,260,40,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6179 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6179
end Delivery.IrregularNine14.P07
