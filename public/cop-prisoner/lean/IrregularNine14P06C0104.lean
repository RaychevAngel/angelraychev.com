import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6240 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 265 112 36 66 148 276), lower := (rows 35 74 133 265 112 36 66 128 256), losses := [] }

theorem u6240 : Upper (D 6) (R 6) [34,72,129,257,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6241 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 133 265 112 36 68 146 274), lower := (rows 35 74 133 265 112 36 68 128 256), losses := [] }

theorem u6241 : Upper (D 6) (R 6) [34,72,129,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6242 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 265 112 36 80 134 262), lower := (rows 35 74 133 265 112 36 80 128 256), losses := [] }

theorem u6242 : Upper (D 6) (R 6) [34,72,129,257,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6242 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6243 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 4, region := 298, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 35 74 133 266 84 36 65 176 304), lower := (rows 35 74 133 266 84 36 65 128 256), losses := [] }

theorem u6243 : Upper (D 6) (R 6) [34,72,129,258,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6244 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 266 84 36 80 161 289), lower := (rows 35 74 133 266 84 36 80 128 256), losses := [] }

theorem u6244 : Upper (D 6) (R 6) [34,72,129,258,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6244 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6245 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 2, region := 112, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 35 74 133 266 84 36 96 145 273), lower := (rows 35 74 133 266 84 36 96 128 256), losses := [] }

theorem u6245 : Upper (D 6) (R 6) [34,72,129,258,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6246 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 133 266 112 36 65 148 276), lower := (rows 35 74 133 266 112 36 65 128 256), losses := [] }

theorem u6246 : Upper (D 6) (R 6) [34,72,129,258,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6247 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 133 266 112 36 68 145 273), lower := (rows 35 74 133 266 112 36 68 128 256), losses := [] }

theorem u6247 : Upper (D 6) (R 6) [34,72,129,258,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6248 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 266 112 36 80 133 261), lower := (rows 35 74 133 266 112 36 80 128 256), losses := [] }

theorem u6248 : Upper (D 6) (R 6) [34,72,129,258,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6248 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6249 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 74 133 268 81 36 66 176 304), lower := (rows 35 74 133 268 81 36 66 128 256), losses := [] }

theorem u6249 : Upper (D 6) (R 6) [34,72,129,260,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6250 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 268 81 36 80 162 290), lower := (rows 35 74 133 268 81 36 80 128 256), losses := [] }

theorem u6250 : Upper (D 6) (R 6) [34,72,129,260,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6250 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6251 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 133 268 81 36 96 146 274), lower := (rows 35 74 133 268 81 36 96 128 256), losses := [] }

theorem u6251 : Upper (D 6) (R 6) [34,72,129,260,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6252 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 74 133 268 84 33 66 176 304), lower := (rows 35 74 133 268 84 33 66 128 256), losses := [] }

theorem u6252 : Upper (D 6) (R 6) [34,72,129,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6253 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 82, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 74 133 268 84 33 80 162 290), lower := (rows 35 74 133 268 84 33 80 128 256), losses := [] }

theorem u6253 : Upper (D 6) (R 6) [34,72,129,260,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6253 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6254 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 266, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 268 84 33 96 146 274), lower := (rows 35 74 133 268 84 33 96 128 256), losses := [] }

theorem u6254 : Upper (D 6) (R 6) [34,72,129,260,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6255 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 4, region := 298, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 35 74 133 280 84 36 65 162 290), lower := (rows 35 74 133 280 84 36 65 128 256), losses := [] }

theorem u6255 : Upper (D 6) (R 6) [34,72,129,272,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6256 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 280 84 36 66 161 289), lower := (rows 35 74 133 280 84 36 66 128 256), losses := [] }

theorem u6256 : Upper (D 6) (R 6) [34,72,129,272,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6257 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 2, region := 112, targets := 1 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 35 74 133 280 84 36 96 131 259), lower := (rows 35 74 133 280 84 36 96 128 256), losses := [] }

theorem u6257 : Upper (D 6) (R 6) [34,72,129,272,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6258 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 74 133 296 81 36 66 148 276), lower := (rows 35 74 133 296 81 36 66 128 256), losses := [] }

theorem u6258 : Upper (D 6) (R 6) [34,72,129,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6259 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 2, region := 80, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 35 74 133 296 81 36 68 146 274), lower := (rows 35 74 133 296 81 36 68 128 256), losses := [] }

theorem u6259 : Upper (D 6) (R 6) [34,72,129,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6260 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 296 81 36 80 134 262), lower := (rows 35 74 133 296 81 36 80 128 256), losses := [] }

theorem u6260 : Upper (D 6) (R 6) [34,72,129,288,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6260 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6261 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 133 296 84 36 65 146 274), lower := (rows 35 74 133 296 84 36 65 128 256), losses := [] }

theorem u6261 : Upper (D 6) (R 6) [34,72,129,288,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6262 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 35 74 133 296 84 36 66 145 273), lower := (rows 35 74 133 296 84 36 66 128 256), losses := [] }

theorem u6262 : Upper (D 6) (R 6) [34,72,129,288,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6263 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 296 84 36 80 131 259), lower := (rows 35 74 133 296 84 36 80 128 256), losses := [] }

theorem u6263 : Upper (D 6) (R 6) [34,72,129,288,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6263 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6264 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 134 13 52 288 65 208 336), lower := (rows 35 74 134 13 52 288 65 128 256), losses := [] }

theorem u6264 : Upper (D 6) (R 6) [34,72,130,5,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6264 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6265 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 74 134 13 52 288 80 193 321), lower := (rows 35 74 134 13 52 288 80 128 256), losses := [] }

theorem u6265 : Upper (D 6) (R 6) [34,72,130,5,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6265 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6266 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 74 134 13 81 288 68 176 304), lower := (rows 35 74 134 13 81 288 68 128 256), losses := [] }

theorem u6266 : Upper (D 6) (R 6) [34,72,130,5,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6266 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6267 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 82, targets := 4 }], pairs := [(1,2)], upper := (rows 35 74 134 13 81 288 80 164 292), lower := (rows 35 74 134 13 81 288 80 128 256), losses := [] }

theorem u6267 : Upper (D 6) (R 6) [34,72,130,5,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6267 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6268 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 13 81 288 96 148 276), lower := (rows 35 74 134 13 81 288 96 128 256), losses := [] }

theorem u6268 : Upper (D 6) (R 6) [34,72,130,5,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6268 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6269 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 436, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 134 13 84 288 65 176 304), lower := (rows 35 74 134 13 84 288 65 128 256), losses := [] }

theorem u6269 : Upper (D 6) (R 6) [34,72,130,5,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6269 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6270 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0)], upper := (rows 35 74 134 13 84 288 80 161 289), lower := (rows 35 74 134 13 84 288 80 128 256), losses := [] }

theorem u6270 : Upper (D 6) (R 6) [34,72,130,5,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6270 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6271 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 368, targets := 2 }], pairs := [(1,0),(4,1)], upper := (rows 35 74 134 13 84 288 96 145 273), lower := (rows 35 74 134 13 84 288 96 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 288 353 128 256), good := (rows 98 90 134 94 84 352 96 128 352) }] }

theorem u6271 : Upper (D 6) (R 6) [34,72,130,5,68,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6271 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6272 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 74 134 13 112 288 65 148 276), lower := (rows 35 74 134 13 112 288 65 128 256), losses := [] }

theorem u6272 : Upper (D 6) (R 6) [34,72,130,5,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6272 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6273 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 74 134 13 112 288 68 145 273), lower := (rows 35 74 134 13 112 288 68 128 256), losses := [] }

theorem u6273 : Upper (D 6) (R 6) [34,72,130,5,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6273 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6274 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 35 74 134 13 112 288 80 133 261), lower := (rows 35 74 134 13 112 288 80 128 256), losses := [] }

theorem u6274 : Upper (D 6) (R 6) [34,72,130,5,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6274 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6275 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 35 74 134 25 336 36 65 164 292), lower := (rows 35 74 134 25 336 36 65 128 256), losses := [] }

theorem u6275 : Upper (D 6) (R 6) [34,72,130,17,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6276 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 35 74 134 25 336 36 68 161 289), lower := (rows 35 74 134 25 336 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 100 100 129 257), good := (rows 505 104 228 409 368 100 100 128 256) }] }

theorem u6276 : Upper (D 6) (R 6) [34,72,130,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6277 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 132, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 134 25 336 36 96 133 261), lower := (rows 35 74 134 25 336 36 96 128 256), losses := [] }

theorem u6277 : Upper (D 6) (R 6) [34,72,130,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6278 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 35 74 134 265 81 36 68 176 304), lower := (rows 35 74 134 265 81 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 17 100 100 145 273), good := (rows 505 104 228 409 505 100 100 128 256) }] }

theorem u6278 : Upper (D 6) (R 6) [34,72,130,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6279 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 82, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 74 134 265 81 36 80 164 292), lower := (rows 35 74 134 265 81 36 80 128 256), losses := [] }

theorem u6279 : Upper (D 6) (R 6) [34,72,130,257,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6279 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6280 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 134 265 81 36 96 148 276), lower := (rows 35 74 134 265 81 36 96 128 256), losses := [] }

theorem u6280 : Upper (D 6) (R 6) [34,72,130,257,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6281 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 180, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 134 265 84 36 65 176 304), lower := (rows 35 74 134 265 84 36 65 128 256), losses := [] }

theorem u6281 : Upper (D 6) (R 6) [34,72,130,257,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6282 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 134 265 84 36 80 161 289), lower := (rows 35 74 134 265 84 36 80 128 256), losses := [] }

theorem u6282 : Upper (D 6) (R 6) [34,72,130,257,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6282 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6283 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 74 134 265 84 36 96 145 273), lower := (rows 35 74 134 265 84 36 96 128 256), losses := [] }

theorem u6283 : Upper (D 6) (R 6) [34,72,130,257,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6284 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 1, region := 180, targets := 1 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 35 74 134 265 112 36 65 148 276), lower := (rows 35 74 134 265 112 36 65 128 256), losses := [] }

theorem u6284 : Upper (D 6) (R 6) [34,72,130,257,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6285 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 134 265 112 36 68 145 273), lower := (rows 35 74 134 265 112 36 68 128 256), losses := [] }

theorem u6285 : Upper (D 6) (R 6) [34,72,130,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6286 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 134 265 112 36 80 133 261), lower := (rows 35 74 134 265 112 36 80 128 256), losses := [] }

theorem u6286 : Upper (D 6) (R 6) [34,72,130,257,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6286 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6287 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 66, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 35 74 148 13 81 288 66 164 292), lower := (rows 35 74 148 13 81 288 66 128 256), losses := [] }

theorem u6287 : Upper (D 6) (R 6) [34,72,144,5,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6287 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6288 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 74 148 13 81 288 68 162 290), lower := (rows 35 74 148 13 81 288 68 128 256), losses := [] }

theorem u6288 : Upper (D 6) (R 6) [34,72,144,5,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6288 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6289 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 142, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 148 13 81 288 96 134 262), lower := (rows 35 74 148 13 81 288 96 128 256), losses := [] }

theorem u6289 : Upper (D 6) (R 6) [34,72,144,5,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6289 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6290 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 74 148 13 112 288 65 134 262), lower := (rows 35 74 148 13 112 288 65 128 256), losses := [] }

theorem u6290 : Upper (D 6) (R 6) [34,72,144,5,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6290 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6291 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 148 13 112 288 66 133 261), lower := (rows 35 74 148 13 112 288 66 128 256), losses := [] }

theorem u6291 : Upper (D 6) (R 6) [34,72,144,5,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6291 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6292 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 74 148 13 112 288 68 131 259), lower := (rows 35 74 148 13 112 288 68 128 256), losses := [] }

theorem u6292 : Upper (D 6) (R 6) [34,72,144,5,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6292 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6293 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 82, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 148 265 81 36 66 164 292), lower := (rows 35 74 148 265 81 36 66 128 256), losses := [] }

theorem u6293 : Upper (D 6) (R 6) [34,72,144,257,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6294 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 264, targets := 68 }], pairs := [(2,0),(3,2),(3,6)], upper := (rows 35 74 148 265 81 36 68 162 290), lower := (rows 35 74 148 265 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 116 116 131 259), good := (rows 482 490 244 392 500 100 100 128 256) }] }

theorem u6294 : Upper (D 6) (R 6) [34,72,144,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6295 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 74 148 265 81 36 96 134 262), lower := (rows 35 74 148 265 81 36 96 128 256), losses := [] }

theorem u6295 : Upper (D 6) (R 6) [34,72,144,257,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6296 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 1, region := 180, targets := 1 }], pairs := [(2,0),(4,1),(4,2)], upper := (rows 35 74 148 265 112 36 65 134 262), lower := (rows 35 74 148 265 112 36 65 128 256), losses := [] }

theorem u6296 : Upper (D 6) (R 6) [34,72,144,257,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6297 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 148 265 112 36 66 133 261), lower := (rows 35 74 148 265 112 36 66 128 256), losses := [] }

theorem u6297 : Upper (D 6) (R 6) [34,72,144,257,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6298 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 74 148 265 112 36 68 131 259), lower := (rows 35 74 148 265 112 36 68 128 256), losses := [] }

theorem u6298 : Upper (D 6) (R 6) [34,72,144,257,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6299 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 148 266 112 36 65 133 261), lower := (rows 35 74 148 266 112 36 65 128 256), losses := [] }

theorem u6299 : Upper (D 6) (R 6) [34,72,144,258,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P06
