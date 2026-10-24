import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7260 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 1, region := 424, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(3,0)], upper := (rows 37 74 84 296 145 34 65 130 386), lower := (rows 37 74 84 296 145 34 65 128 256), losses := [] }

theorem u7260 : Upper (D 7) (R 7) [36,72,80,288,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7261 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 296 145 34 66 129 385), lower := (rows 37 74 84 296 145 34 66 128 256), losses := [] }

theorem u7261 : Upper (D 7) (R 7) [36,72,80,288,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7262 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 37 74 84 296 145 34 192 131 259), lower := (rows 37 74 84 296 145 34 192 128 256), losses := [] }

theorem u7262 : Upper (D 7) (R 7) [36,72,80,288,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7263 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 84 296 146 33 65 130 386), lower := (rows 37 74 84 296 146 33 65 128 256), losses := [] }

theorem u7263 : Upper (D 7) (R 7) [36,72,80,288,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7264 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 84 296 146 33 66 129 385), lower := (rows 37 74 84 296 146 33 66 128 256), losses := [] }

theorem u7264 : Upper (D 7) (R 7) [36,72,80,288,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7265 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 37 74 84 296 146 33 192 131 259), lower := (rows 37 74 84 296 146 33 192 128 256), losses := [] }

theorem u7265 : Upper (D 7) (R 7) [36,72,80,288,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7266 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 1, region := 424, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(3,0)], upper := (rows 37 74 84 392 19 160 65 162 290), lower := (rows 37 74 84 392 19 160 65 128 256), losses := [] }

theorem u7266 : Upper (D 7) (R 7) [36,72,80,384,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7267 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 84 392 19 160 66 161 289), lower := (rows 37 74 84 392 19 160 66 128 256), losses := [] }

theorem u7267 : Upper (D 7) (R 7) [36,72,80,384,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7268 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 1 },{ cop := 4, region := 392, targets := 32 },{ cop := 4, region := 392, targets := 64 }], pairs := [(1,0),(2,0),(3,5),(3,6)], upper := (rows 37 74 84 392 19 160 96 131 259), lower := (rows 37 74 84 392 19 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 168 235 128 256), good := (rows 100 106 84 490 86 224 96 224 256) }] }

theorem u7268 : Upper (D 7) (R 7) [36,72,80,384,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7269 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 1, region := 424, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(3,0)], upper := (rows 37 74 84 392 145 34 65 162 290), lower := (rows 37 74 84 392 145 34 65 128 256), losses := [] }

theorem u7269 : Upper (D 7) (R 7) [36,72,80,384,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7270 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 392 145 34 66 161 289), lower := (rows 37 74 84 392 145 34 66 128 256), losses := [] }

theorem u7270 : Upper (D 7) (R 7) [36,72,80,384,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7271 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 74 84 392 145 34 96 131 259), lower := (rows 37 74 84 392 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 42 107 128 256), good := (rows 100 106 84 490 212 98 96 128 256) },{ target := 1, region := (rows 1 0 20 8 16 32 97 128 256), good := (rows 101 72 84 392 213 96 96 128 256) }] }

theorem u7271 : Upper (D 7) (R 7) [36,72,80,384,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7271 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7272 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 392 176 34 65 131 259), lower := (rows 37 74 84 392 176 34 65 128 256), losses := [] }

theorem u7272 : Upper (D 7) (R 7) [36,72,80,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7273 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 392 176 34 66 129 257), lower := (rows 37 74 84 392 176 34 66 128 256), losses := [] }

theorem u7273 : Upper (D 7) (R 7) [36,72,80,384,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7274 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 133 138 50 288 65 208 336), lower := (rows 37 74 133 138 50 288 65 128 256), losses := [] }

theorem u7274 : Upper (D 7) (R 7) [36,72,129,130,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7274 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7275 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 421, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 74 133 138 50 288 80 193 321), lower := (rows 37 74 133 138 50 288 80 128 256), losses := [] }

theorem u7275 : Upper (D 7) (R 7) [36,72,129,130,34,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7275 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7276 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 138 112 33 320 146 274), lower := (rows 37 74 133 138 112 33 320 128 256), losses := [] }

theorem u7276 : Upper (D 7) (R 7) [36,72,129,130,96,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7276 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7277 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 469, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 133 138 112 34 320 145 273), lower := (rows 37 74 133 138 112 34 320 128 256), losses := [] }

theorem u7277 : Upper (D 7) (R 7) [36,72,129,130,96,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7277 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7278 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 37 74 133 138 112 48 320 131 259), lower := (rows 37 74 133 138 112 48 320 128 256), losses := [] }

theorem u7278 : Upper (D 7) (R 7) [36,72,129,130,96,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7278 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7279 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 133 138 273 48 66 224 352), lower := (rows 37 74 133 138 273 48 66 128 256), losses := [] }

theorem u7279 : Upper (D 7) (R 7) [36,72,129,130,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7279 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7280 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 74 133 138 273 48 96 194 322), lower := (rows 37 74 133 138 273 48 96 128 256), losses := [] }

theorem u7280 : Upper (D 7) (R 7) [36,72,129,130,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7280 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7281 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 138 304 96 65 146 274), lower := (rows 37 74 133 138 304 96 65 128 256), losses := [] }

theorem u7281 : Upper (D 7) (R 7) [36,72,129,130,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7282 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 405, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 138 304 96 66 145 273), lower := (rows 37 74 133 138 304 96 66 128 256), losses := [] }

theorem u7282 : Upper (D 7) (R 7) [36,72,129,130,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7283 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 37 74 133 138 304 96 80 131 259), lower := (rows 37 74 133 138 304 96 80 128 256), losses := [] }

theorem u7283 : Upper (D 7) (R 7) [36,72,129,130,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7283 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7284 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 389, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 19 96 66 416 288), lower := (rows 37 74 133 152 19 96 66 128 256), losses := [] }

theorem u7284 : Upper (D 7) (R 7) [36,72,129,144,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7285 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 37 74 133 152 19 96 96 386 258), lower := (rows 37 74 133 152 19 96 96 128 256), losses := [] }

theorem u7285 : Upper (D 7) (R 7) [36,72,129,144,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7286 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 74 133 152 19 96 320 162 290), lower := (rows 37 74 133 152 19 96 320 128 256), losses := [] }

theorem u7286 : Upper (D 7) (R 7) [36,72,129,144,3,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7286 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7287 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 133 152 50 288 65 194 322), lower := (rows 37 74 133 152 50 288 65 128 256), losses := [] }

theorem u7287 : Upper (D 7) (R 7) [36,72,129,144,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7287 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7288 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 133 152 50 288 66 193 321), lower := (rows 37 74 133 152 50 288 66 128 256), losses := [] }

theorem u7288 : Upper (D 7) (R 7) [36,72,129,144,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7288 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7289 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 74 133 152 112 288 65 130 258), lower := (rows 37 74 133 152 112 288 65 128 256), losses := [] }

theorem u7289 : Upper (D 7) (R 7) [36,72,129,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7289 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7290 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 133 152 112 288 66 131 259), lower := (rows 37 74 133 152 112 288 66 128 256), losses := [] }

theorem u7290 : Upper (D 7) (R 7) [36,72,129,144,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7290 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7291 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 66, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 74 133 152 273 96 66 162 290), lower := (rows 37 74 133 152 273 96 66 128 256), losses := [] }

theorem u7291 : Upper (D 7) (R 7) [36,72,129,144,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7292 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,1),(0,7),(1,0),(3,0)], upper := (rows 37 74 133 152 273 96 96 130 258), lower := (rows 37 74 133 152 273 96 96 128 256), losses := [] }

theorem u7292 : Upper (D 7) (R 7) [36,72,129,144,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7293 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 152 274 96 65 162 290), lower := (rows 37 74 133 152 274 96 65 128 256), losses := [] }

theorem u7293 : Upper (D 7) (R 7) [36,72,129,144,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7294 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 274 96 66 161 289), lower := (rows 37 74 133 152 274 96 66 128 256), losses := [] }

theorem u7294 : Upper (D 7) (R 7) [36,72,129,144,258,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7295 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 97, targets := 130 },{ cop := 3, region := 98, targets := 129 }], pairs := [(0,1),(0,7),(1,0),(1,7)], upper := (rows 37 74 133 152 274 96 96 131 259), lower := (rows 37 74 133 152 274 96 96 128 256), losses := [] }

theorem u7295 : Upper (D 7) (R 7) [36,72,129,144,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7296 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 304, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 37 74 133 152 304 34 65 194 322), lower := (rows 37 74 133 152 304 34 65 128 256), losses := [] }

theorem u7296 : Upper (D 7) (R 7) [36,72,129,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7297 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(1,7),(2,5)], upper := (rows 37 74 133 152 304 34 66 193 321), lower := (rows 37 74 133 152 304 34 66 128 256), losses := [{ target := 5, region := (rows 1 10 5 8 16 0 106 129 257), good := (rows 453 74 389 218 336 66 66 128 256) }] }

theorem u7297 : Upper (D 7) (R 7) [36,72,129,144,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7298 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 152 304 96 65 130 258), lower := (rows 37 74 133 152 304 96 65 128 256), losses := [] }

theorem u7298 : Upper (D 7) (R 7) [36,72,129,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7298 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7299 : Route 9 := (fun mask => (mask,id))

def c7299 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7299 : Upper (D 7) (R 7) [36,72,129,144,288,64,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,144,288,64,2] 13 (by decide) (choices 1) [1,2] r7299 c7299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u530
  · exact u531

def b7300 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 152 336 34 65 162 290), lower := (rows 37 74 133 152 336 34 65 128 256), losses := [] }

theorem u7300 : Upper (D 7) (R 7) [36,72,129,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7301 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 152 336 34 66 161 289), lower := (rows 37 74 133 152 336 34 66 128 256), losses := [] }

theorem u7301 : Upper (D 7) (R 7) [36,72,129,144,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7302 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 98, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 74 133 152 336 34 96 131 259), lower := (rows 37 74 133 152 336 34 96 128 256), losses := [] }

theorem u7302 : Upper (D 7) (R 7) [36,72,129,144,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7303 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 265 112 34 66 144 400), lower := (rows 37 74 133 265 112 34 66 128 256), losses := [] }

theorem u7303 : Upper (D 7) (R 7) [36,72,129,257,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7304 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 133 265 112 34 80 130 386), lower := (rows 37 74 133 265 112 34 80 128 256), losses := [] }

theorem u7304 : Upper (D 7) (R 7) [36,72,129,257,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7304 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7305 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 48, targets := 128 }], pairs := [(1,0),(4,0),(4,1),(4,7)], upper := (rows 37 74 133 265 112 34 192 146 274), lower := (rows 37 74 133 265 112 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 32 196 128 256), good := (rows 117 72 213 281 112 32 192 192 256) }] }

theorem u7305 : Upper (D 7) (R 7) [36,72,129,257,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7306 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 66, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 37 74 133 265 208 34 66 176 304), lower := (rows 37 74 133 265 208 34 66 128 256), losses := [] }

theorem u7306 : Upper (D 7) (R 7) [36,72,129,257,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7307 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 133 265 208 34 80 162 290), lower := (rows 37 74 133 265 208 34 80 128 256), losses := [] }

theorem u7307 : Upper (D 7) (R 7) [36,72,129,257,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7307 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7308 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 1, region := 144, targets := 32 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 74 133 265 208 34 96 146 274), lower := (rows 37 74 133 265 208 34 96 128 256), losses := [] }

theorem u7308 : Upper (D 7) (R 7) [36,72,129,257,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7308 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7309 : PairBound 9 := { available := 160, camps := [{ cop := 8, region := 74, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 133 266 81 48 66 160 416), lower := (rows 37 74 133 266 81 48 66 128 256), losses := [] }

theorem u7309 : Upper (D 7) (R 7) [36,72,129,258,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7309 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7310 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 74 133 266 81 48 96 130 386), lower := (rows 37 74 133 266 81 48 96 128 256), losses := [] }

theorem u7310 : Upper (D 7) (R 7) [36,72,129,258,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7310 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7311 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 133 266 81 48 192 162 290), lower := (rows 37 74 133 266 81 48 192 128 256), losses := [] }

theorem u7311 : Upper (D 7) (R 7) [36,72,129,258,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7311 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7312 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 74 133 266 146 96 65 176 304), lower := (rows 37 74 133 266 146 96 65 128 256), losses := [] }

theorem u7312 : Upper (D 7) (R 7) [36,72,129,258,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7313 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 266 146 96 80 161 289), lower := (rows 37 74 133 266 146 96 80 128 256), losses := [] }

theorem u7313 : Upper (D 7) (R 7) [36,72,129,258,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7313 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7314 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 133 266 146 96 96 145 273), lower := (rows 37 74 133 266 146 96 96 128 256), losses := [] }

theorem u7314 : Upper (D 7) (R 7) [36,72,129,258,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7315 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 6, region := 442, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 74 133 266 208 34 65 176 304), lower := (rows 37 74 133 266 208 34 65 128 256), losses := [] }

theorem u7315 : Upper (D 7) (R 7) [36,72,129,258,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7316 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 74 133 266 208 34 80 161 289), lower := (rows 37 74 133 266 208 34 80 128 256), losses := [] }

theorem u7316 : Upper (D 7) (R 7) [36,72,129,258,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7316 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7317 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 74 133 266 208 34 96 145 273), lower := (rows 37 74 133 266 208 34 96 128 256), losses := [] }

theorem u7317 : Upper (D 7) (R 7) [36,72,129,258,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7318 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 133, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 280 19 96 66 160 416), lower := (rows 37 74 133 280 19 96 66 128 256), losses := [] }

theorem u7318 : Upper (D 7) (R 7) [36,72,129,272,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7319 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 37 74 133 280 19 96 96 130 386), lower := (rows 37 74 133 280 19 96 96 128 256), losses := [] }

theorem u7319 : Upper (D 7) (R 7) [36,72,129,272,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7319
end Delivery.IrregularNine14.P07
