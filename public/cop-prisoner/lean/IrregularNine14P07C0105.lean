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

def b6300 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 68, targets := 130 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(2,7),(3,5),(4,5)], upper := (rows 35 262 100 26 145 160 65 200 328), lower := (rows 35 262 100 26 145 160 65 128 256), losses := [] }

theorem u6300 : Upper (D 7) (R 7) [34,260,96,18,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6301 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 259, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 262 100 26 145 160 72 193 321), lower := (rows 35 262 100 26 145 160 72 128 256), losses := [] }

theorem u6301 : Upper (D 7) (R 7) [34,260,96,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6301 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6302 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7),(3,5),(4,5)], upper := (rows 35 262 100 73 145 48 66 136 392), lower := (rows 35 262 100 73 145 48 66 128 256), losses := [] }

theorem u6302 : Upper (D 7) (R 7) [34,260,96,65,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6302 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6303 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 262 100 73 145 48 72 130 386), lower := (rows 35 262 100 73 145 48 72 128 256), losses := [] }

theorem u6303 : Upper (D 7) (R 7) [34,260,96,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6303 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6304 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 100 73 145 48 192 138 266), lower := (rows 35 262 100 73 145 48 192 128 256), losses := [] }

theorem u6304 : Upper (D 7) (R 7) [34,260,96,65,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6305 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,5),(3,7),(4,5)], upper := (rows 35 262 100 73 145 160 66 152 280), lower := (rows 35 262 100 73 145 160 66 128 256), losses := [] }

theorem u6305 : Upper (D 7) (R 7) [34,260,96,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6306 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 100 73 145 160 72 146 274), lower := (rows 35 262 100 73 145 160 72 128 256), losses := [] }

theorem u6306 : Upper (D 7) (R 7) [34,260,96,65,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6306 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6307 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 100 73 145 160 80 138 266), lower := (rows 35 262 100 73 145 160 80 128 256), losses := [] }

theorem u6307 : Upper (D 7) (R 7) [34,260,96,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6307 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6308 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 100 73 146 160 65 152 280), lower := (rows 35 262 100 73 146 160 65 128 256), losses := [] }

theorem u6308 : Upper (D 7) (R 7) [34,260,96,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6309 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 262 100 73 146 160 72 145 273), lower := (rows 35 262 100 73 146 160 72 128 256), losses := [] }

theorem u6309 : Upper (D 7) (R 7) [34,260,96,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6309 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6310 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 100 73 146 160 80 137 265), lower := (rows 35 262 100 73 146 160 80 128 256), losses := [] }

theorem u6310 : Upper (D 7) (R 7) [34,260,96,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6310 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6311 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1),(3,7)], upper := (rows 35 262 100 73 152 160 65 146 274), lower := (rows 35 262 100 73 152 160 65 128 256), losses := [] }

theorem u6311 : Upper (D 7) (R 7) [34,260,96,65,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6312 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7),(3,5),(3,7),(4,5)], upper := (rows 35 262 100 73 152 160 66 145 273), lower := (rows 35 262 100 73 152 160 66 128 256), losses := [] }

theorem u6312 : Upper (D 7) (R 7) [34,260,96,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6313 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 100 73 152 160 80 131 259), lower := (rows 35 262 100 73 152 160 80 128 256), losses := [] }

theorem u6313 : Upper (D 7) (R 7) [34,260,96,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6313 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6314 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 262 100 137 208 40 65 146 274), lower := (rows 35 262 100 137 208 40 65 128 256), losses := [] }

theorem u6314 : Upper (D 7) (R 7) [34,260,96,129,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6314 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6315 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 35 262 100 137 208 40 66 145 273), lower := (rows 35 262 100 137 208 40 66 128 256), losses := [] }

theorem u6315 : Upper (D 7) (R 7) [34,260,96,129,192,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6315 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6316 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 262 100 137 208 40 80 131 259), lower := (rows 35 262 100 137 208 40 80 128 256), losses := [] }

theorem u6316 : Upper (D 7) (R 7) [34,260,96,129,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6316 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6317 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 262 196 25 112 40 65 130 386), lower := (rows 35 262 196 25 112 40 65 128 256), losses := [] }

theorem u6317 : Upper (D 7) (R 7) [34,260,192,17,96,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6317 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6318 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 262 196 25 112 40 66 129 385), lower := (rows 35 262 196 25 112 40 66 128 256), losses := [] }

theorem u6318 : Upper (D 7) (R 7) [34,260,192,17,96,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6318 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6319 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 196 25 112 40 192 131 259), lower := (rows 35 262 196 25 112 40 192 128 256), losses := [] }

theorem u6319 : Upper (D 7) (R 7) [34,260,192,17,96,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6319 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6320 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 262 196 26 81 33 72 160 416), lower := (rows 35 262 196 26 81 33 72 128 256), losses := [] }

theorem u6320 : Upper (D 7) (R 7) [34,260,192,18,65,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6320 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6321 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 26 81 33 96 136 392), lower := (rows 35 262 196 26 81 33 96 128 256), losses := [] }

theorem u6321 : Upper (D 7) (R 7) [34,260,192,18,65,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6322 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 262 196 26 81 33 192 168 296), lower := (rows 35 262 196 26 81 33 192 128 256), losses := [] }

theorem u6322 : Upper (D 7) (R 7) [34,260,192,18,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6323 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 35 262 196 26 81 160 65 168 296), lower := (rows 35 262 196 26 81 160 65 128 256), losses := [] }

theorem u6323 : Upper (D 7) (R 7) [34,260,192,18,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6324 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 35 262 196 26 81 160 72 161 289), lower := (rows 35 262 196 26 81 160 72 128 256), losses := [] }

theorem u6324 : Upper (D 7) (R 7) [34,260,192,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6324 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6325 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(1,5),(2,5),(3,5),(3,7)], upper := (rows 35 262 196 26 81 160 96 137 265), lower := (rows 35 262 196 26 81 160 96 128 256), losses := [] }

theorem u6325 : Upper (D 7) (R 7) [34,260,192,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6326 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 26 112 33 65 136 392), lower := (rows 35 262 196 26 112 33 65 128 256), losses := [] }

theorem u6326 : Upper (D 7) (R 7) [34,260,192,18,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6327 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 121, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 262 196 26 112 33 72 129 385), lower := (rows 35 262 196 26 112 33 72 128 256), losses := [] }

theorem u6327 : Upper (D 7) (R 7) [34,260,192,18,96,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6327 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6328 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 35 262 196 26 112 33 192 137 265), lower := (rows 35 262 196 26 112 33 192 128 256), losses := [] }

theorem u6328 : Upper (D 7) (R 7) [34,260,192,18,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6329 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 35 262 196 56 81 160 65 138 266), lower := (rows 35 262 196 56 81 160 65 128 256), losses := [] }

theorem u6329 : Upper (D 7) (R 7) [34,260,192,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6330 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1),(3,1),(3,7),(4,7)], upper := (rows 35 262 196 56 81 160 66 137 265), lower := (rows 35 262 196 56 81 160 66 128 256), losses := [] }

theorem u6330 : Upper (D 7) (R 7) [34,260,192,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6331 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 88, targets := 2 },{ cop := 0, region := 88, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 262 196 56 81 160 72 131 259), lower := (rows 35 262 196 56 81 160 72 128 256), losses := [] }

theorem u6331 : Upper (D 7) (R 7) [34,260,192,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6331 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6332 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 35 262 196 73 145 40 66 176 304), lower := (rows 35 262 196 73 145 40 66 128 256), losses := [] }

theorem u6332 : Upper (D 7) (R 7) [34,260,192,65,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6332 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6333 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 262 196 73 145 40 80 162 290), lower := (rows 35 262 196 73 145 40 80 128 256), losses := [] }

theorem u6333 : Upper (D 7) (R 7) [34,260,192,65,129,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6333 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6334 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 196 73 145 40 96 146 274), lower := (rows 35 262 196 73 145 40 96 128 256), losses := [] }

theorem u6334 : Upper (D 7) (R 7) [34,260,192,65,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6334 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6335 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 196 73 146 33 72 176 304), lower := (rows 35 262 196 73 146 33 72 128 256), losses := [] }

theorem u6335 : Upper (D 7) (R 7) [34,260,192,65,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6335 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6336 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 196 73 146 33 80 168 296), lower := (rows 35 262 196 73 146 33 80 128 256), losses := [] }

theorem u6336 : Upper (D 7) (R 7) [34,260,192,65,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6336 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6337 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 73 146 33 96 152 280), lower := (rows 35 262 196 73 146 33 96 128 256), losses := [] }

theorem u6337 : Upper (D 7) (R 7) [34,260,192,65,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6338 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 3, region := 180, targets := 2 }], pairs := [(0,7),(2,1),(3,7),(4,1)], upper := (rows 35 262 196 73 152 33 66 176 304), lower := (rows 35 262 196 73 152 33 66 128 256), losses := [] }

theorem u6338 : Upper (D 7) (R 7) [34,260,192,65,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6339 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 196 73 152 33 80 162 290), lower := (rows 35 262 196 73 152 33 80 128 256), losses := [] }

theorem u6339 : Upper (D 7) (R 7) [34,260,192,65,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6339 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6340 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 73 152 33 96 146 274), lower := (rows 35 262 196 73 152 33 96 128 256), losses := [] }

theorem u6340 : Upper (D 7) (R 7) [34,260,192,65,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6341 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 262 196 73 152 48 65 162 290), lower := (rows 35 262 196 73 152 48 65 128 256), losses := [] }

theorem u6341 : Upper (D 7) (R 7) [34,260,192,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6341 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6342 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 180, targets := 2 },{ cop := 0, region := 72, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 262 196 73 152 48 66 161 289), lower := (rows 35 262 196 73 152 48 66 128 256), losses := [] }

theorem u6342 : Upper (D 7) (R 7) [34,260,192,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6342 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6343 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 196 73 152 48 96 131 259), lower := (rows 35 262 196 73 152 48 96 128 256), losses := [] }

theorem u6343 : Upper (D 7) (R 7) [34,260,192,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6343 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6344 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 3, region := 180, targets := 2 }], pairs := [(0,7),(2,1),(3,7),(4,1)], upper := (rows 35 262 196 73 176 33 66 152 280), lower := (rows 35 262 196 73 176 33 66 128 256), losses := [] }

theorem u6344 : Upper (D 7) (R 7) [34,260,192,65,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6345 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 196 73 176 33 72 146 274), lower := (rows 35 262 196 73 176 33 72 128 256), losses := [] }

theorem u6345 : Upper (D 7) (R 7) [34,260,192,65,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6345 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6346 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 262 196 73 176 33 80 138 266), lower := (rows 35 262 196 73 176 33 80 128 256), losses := [] }

theorem u6346 : Upper (D 7) (R 7) [34,260,192,65,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6346 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6347 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 262 196 73 176 40 65 146 274), lower := (rows 35 262 196 73 176 40 65 128 256), losses := [] }

theorem u6347 : Upper (D 7) (R 7) [34,260,192,65,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6347 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6348 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 35 262 196 73 176 40 66 145 273), lower := (rows 35 262 196 73 176 40 66 128 256), losses := [] }

theorem u6348 : Upper (D 7) (R 7) [34,260,192,65,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6348 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6349 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 262 196 73 176 40 80 131 259), lower := (rows 35 262 196 73 176 40 80 128 256), losses := [] }

theorem u6349 : Upper (D 7) (R 7) [34,260,192,65,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6349 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6350 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 262 196 74 152 33 65 176 304), lower := (rows 35 262 196 74 152 33 65 128 256), losses := [] }

theorem u6350 : Upper (D 7) (R 7) [34,260,192,66,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6351 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 196 74 152 33 80 161 289), lower := (rows 35 262 196 74 152 33 80 128 256), losses := [] }

theorem u6351 : Upper (D 7) (R 7) [34,260,192,66,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6351 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6352 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 262 196 74 152 33 96 145 273), lower := (rows 35 262 196 74 152 33 96 128 256), losses := [] }

theorem u6352 : Upper (D 7) (R 7) [34,260,192,66,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6353 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 105, targets := 128 },{ cop := 3, region := 177, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 262 196 74 176 33 65 152 280), lower := (rows 35 262 196 74 176 33 65 128 256), losses := [] }

theorem u6353 : Upper (D 7) (R 7) [34,260,192,66,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6354 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 196 74 176 33 72 145 273), lower := (rows 35 262 196 74 176 33 72 128 256), losses := [] }

theorem u6354 : Upper (D 7) (R 7) [34,260,192,66,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6354 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6355 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 262 196 74 176 33 80 137 265), lower := (rows 35 262 196 74 176 33 80 128 256), losses := [] }

theorem u6355 : Upper (D 7) (R 7) [34,260,192,66,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6355 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6356 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 88 176 33 65 138 266), lower := (rows 35 262 196 88 176 33 65 128 256), losses := [] }

theorem u6356 : Upper (D 7) (R 7) [34,260,192,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r6357 : Route 9 := (fun mask => (mask,id))

def c6357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6357 : Upper (D 7) (R 7) [34,260,192,80,160,1,2] 13 := by
  apply FastRouting.sound _ _ [34,260,192,80,160,1,2] 13 (by decide) (choices 1) [1,8] r6357 c6357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u466
  · exact u467

def b6358 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 262 196 88 176 33 72 131 259), lower := (rows 35 262 196 88 176 33 72 128 256), losses := [] }

theorem u6358 : Upper (D 7) (R 7) [34,260,192,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6358 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6359 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 35 322 13 26 84 160 65 160 416), lower := (rows 35 322 13 26 84 160 65 128 256), losses := [] }

theorem u6359 : Upper (D 7) (R 7) [34,320,9,18,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6359
end Delivery.IrregularNine14.P07
