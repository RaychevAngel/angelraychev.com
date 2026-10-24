import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4200 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 21 42 112 160 192 194 322), lower := (rows 13 259 21 42 112 160 192 128 256), losses := [] }

theorem u4200 : Upper (D 7) (R 7) [12,257,17,34,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4201 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 1, region := 104, targets := 128 },{ cop := 5, region := 144, targets := 2 }], pairs := [(3,0),(3,7),(4,0),(4,1)], upper := (rows 13 259 21 42 208 96 66 160 416), lower := (rows 13 259 21 42 208 96 66 128 256), losses := [] }

theorem u4201 : Upper (D 7) (R 7) [12,257,17,34,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4202 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 386, targets := 96 },{ cop := 1, region := 248, targets := 1 }], pairs := [(1,5),(1,6),(3,0),(4,0)], upper := (rows 13 259 21 42 208 96 96 130 386), lower := (rows 13 259 21 42 208 96 96 128 256), losses := [] }

theorem u4202 : Upper (D 7) (R 7) [12,257,17,34,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4203 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 21 42 208 96 192 162 290), lower := (rows 13 259 21 42 208 96 192 128 256), losses := [] }

theorem u4203 : Upper (D 7) (R 7) [12,257,17,34,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4204 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,7)], upper := (rows 13 259 21 104 50 160 66 192 448), lower := (rows 13 259 21 104 50 160 66 128 256), losses := [] }

theorem u4204 : Upper (D 7) (R 7) [12,257,17,96,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4205 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 259 21 104 50 160 192 194 322), lower := (rows 13 259 21 104 50 160 192 128 256), losses := [] }

theorem u4205 : Upper (D 7) (R 7) [12,257,17,96,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4206 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5),(4,5)], upper := (rows 13 259 21 104 146 34 96 192 448), lower := (rows 13 259 21 104 146 34 96 128 256), losses := [] }

theorem u4206 : Upper (D 7) (R 7) [12,257,17,96,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4207 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 5, region := 200, targets := 2 }], pairs := [(1,7),(3,0),(3,1),(4,0)], upper := (rows 13 259 21 104 146 34 192 224 352), lower := (rows 13 259 21 104 146 34 192 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 55 64 0 264), good := (rows 303 291 55 360 50 34 64 0 256) }] }

theorem u4207 : Upper (D 7) (R 7) [12,257,17,96,130,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4208 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 21 104 146 96 192 162 290), lower := (rows 13 259 21 104 146 96 192 128 256), losses := [] }

theorem u4208 : Upper (D 7) (R 7) [12,257,17,96,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4209 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 149, targets := 2 },{ cop := 1, region := 104, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 259 21 104 176 34 66 192 448), lower := (rows 13 259 21 104 176 34 66 128 256), losses := [] }

theorem u4209 : Upper (D 7) (R 7) [12,257,17,96,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4210 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 13 259 21 104 176 34 192 194 322), lower := (rows 13 259 21 104 176 34 192 128 256), losses := [] }

theorem u4210 : Upper (D 7) (R 7) [12,257,17,96,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4211 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 244, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 6, region := 176, targets := 2 }], pairs := [(1,5),(2,0),(4,0),(4,1)], upper := (rows 13 259 22 41 112 160 66 192 448), lower := (rows 13 259 22 41 112 160 66 128 256), losses := [] }

theorem u4211 : Upper (D 7) (R 7) [12,257,18,33,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4212 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 22 41 112 160 192 194 322), lower := (rows 13 259 22 41 112 160 192 128 256), losses := [] }

theorem u4212 : Upper (D 7) (R 7) [12,257,18,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4213 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 4, region := 386, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 13 259 22 42 81 160 96 192 448), lower := (rows 13 259 22 42 81 160 96 128 256), losses := [] }

theorem u4213 : Upper (D 7) (R 7) [12,257,18,34,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4214 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 232, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,1)], upper := (rows 13 259 22 42 81 160 192 224 352), lower := (rows 13 259 22 42 81 160 192 128 256), losses := [{ target := 5, region := (rows 9 2 12 8 24 0 224 128 256), good := (rows 29 259 22 95 81 192 192 192 256) }] }

theorem u4214 : Upper (D 7) (R 7) [12,257,18,34,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4215 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 6, region := 176, targets := 1 }], pairs := [(0,7),(2,7),(4,0),(4,7)], upper := (rows 13 259 22 42 112 160 65 192 448), lower := (rows 13 259 22 42 112 160 65 128 256), losses := [] }

theorem u4215 : Upper (D 7) (R 7) [12,257,18,34,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4216 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 22 42 112 160 192 193 321), lower := (rows 13 259 22 42 112 160 192 128 256), losses := [] }

theorem u4216 : Upper (D 7) (R 7) [12,257,18,34,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4217 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 454, targets := 32 },{ cop := 6, region := 168, targets := 3 }], pairs := [(1,5),(2,5),(3,0),(3,1)], upper := (rows 13 259 22 104 49 160 66 192 448), lower := (rows 13 259 22 104 49 160 66 128 256), losses := [] }

theorem u4217 : Upper (D 7) (R 7) [12,257,18,96,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4218 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 259 22 104 49 160 192 194 322), lower := (rows 13 259 22 104 49 160 192 128 256), losses := [] }

theorem u4218 : Upper (D 7) (R 7) [12,257,18,96,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4219 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5),(4,5)], upper := (rows 13 259 22 104 145 34 96 192 448), lower := (rows 13 259 22 104 145 34 96 128 256), losses := [] }

theorem u4219 : Upper (D 7) (R 7) [12,257,18,96,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4220 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 200, targets := 3 }], pairs := [(1,7),(3,0),(3,1),(4,1)], upper := (rows 13 259 22 104 145 34 192 224 352), lower := (rows 13 259 22 104 145 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 40 17 32 249 168 296), good := (rows 477 337 84 488 209 488 192 192 256) },{ target := 7, region := (rows 1 3 20 8 16 55 64 0 264), good := (rows 303 291 54 360 55 34 64 0 256) }] }

theorem u4220 : Upper (D 7) (R 7) [12,257,18,96,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4221 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 259 22 104 145 96 192 162 290), lower := (rows 13 259 22 104 145 96 192 128 256), losses := [] }

theorem u4221 : Upper (D 7) (R 7) [12,257,18,96,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4222 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 105, targets := 128 },{ cop := 3, region := 144, targets := 3 }], pairs := [(0,7),(3,7),(4,0),(4,1)], upper := (rows 13 259 22 104 176 33 66 192 448), lower := (rows 13 259 22 104 176 33 66 128 256), losses := [] }

theorem u4222 : Upper (D 7) (R 7) [12,257,18,96,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4223 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 72, targets := 3 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(3,0),(3,1)], upper := (rows 13 259 22 104 176 33 192 194 322), lower := (rows 13 259 22 104 176 33 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 28 16 39 208 128 256), good := (rows 45 289 125 104 248 33 192 192 256) }] }

theorem u4223 : Upper (D 7) (R 7) [12,257,18,96,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4224 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 105, targets := 128 },{ cop := 3, region := 144, targets := 3 }], pairs := [(0,7),(3,7),(4,0),(4,1)], upper := (rows 13 259 22 104 176 34 65 192 448), lower := (rows 13 259 22 104 176 34 65 128 256), losses := [] }

theorem u4224 : Upper (D 7) (R 7) [12,257,18,96,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4225 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 3 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,1),(1,5),(3,0),(3,1)], upper := (rows 13 259 22 104 176 34 192 193 321), lower := (rows 13 259 22 104 176 34 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 56 48 32 247 135 263), good := (rows 461 449 477 120 248 504 192 192 256) }] }

theorem u4225 : Upper (D 7) (R 7) [12,257,18,96,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4226 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 259 37 74 50 160 80 192 448), lower := (rows 13 259 37 74 50 160 80 128 256), losses := [] }

theorem u4226 : Upper (D 7) (R 7) [12,257,33,66,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4226 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4227 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,1),(3,0),(3,5),(4,0)], upper := (rows 13 259 37 74 50 160 192 208 336), lower := (rows 13 259 37 74 50 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 240 240 144 272), good := (rows 13 257 101 109 496 224 224 224 256) }] }

theorem u4227 : Upper (D 7) (R 7) [12,257,33,66,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4228 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 181, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 259 37 74 112 160 66 144 400), lower := (rows 13 259 37 74 112 160 66 128 256), losses := [] }

theorem u4228 : Upper (D 7) (R 7) [12,257,33,66,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4229 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 13 259 37 74 112 160 80 130 386), lower := (rows 13 259 37 74 112 160 80 128 256), losses := [] }

theorem u4229 : Upper (D 7) (R 7) [12,257,33,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4229 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4230 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 37 74 112 160 192 146 274), lower := (rows 13 259 37 74 112 160 192 128 256), losses := [] }

theorem u4230 : Upper (D 7) (R 7) [12,257,33,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4231 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 259 37 74 146 48 96 192 448), lower := (rows 13 259 37 74 146 48 96 128 256), losses := [] }

theorem u4231 : Upper (D 7) (R 7) [12,257,33,66,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4231 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4232 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 13 259 37 74 146 48 192 224 352), lower := (rows 13 259 37 74 146 48 192 128 256), losses := [] }

theorem u4232 : Upper (D 7) (R 7) [12,257,33,66,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4233 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(3,0),(4,0)], upper := (rows 13 259 37 74 146 160 80 224 352), lower := (rows 13 259 37 74 146 160 80 128 256), losses := [] }

theorem u4233 : Upper (D 7) (R 7) [12,257,33,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4233 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4234 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 144, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 13 259 37 74 146 160 96 208 336), lower := (rows 13 259 37 74 146 160 96 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 25 0 64 136 264), good := (rows 415 275 23 474 146 128 64 128 256) }] }

theorem u4234 : Upper (D 7) (R 7) [12,257,33,66,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4235 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 181, targets := 2 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 13 259 37 74 208 160 66 176 304), lower := (rows 13 259 37 74 208 160 66 128 256), losses := [] }

theorem u4235 : Upper (D 7) (R 7) [12,257,33,66,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4236 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 259 37 74 208 160 80 162 290), lower := (rows 13 259 37 74 208 160 80 128 256), losses := [] }

theorem u4236 : Upper (D 7) (R 7) [12,257,33,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4236 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4237 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 144, targets := 32 },{ cop := 5, region := 80, targets := 2 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 259 37 74 208 160 96 146 274), lower := (rows 13 259 37 74 208 160 96 128 256), losses := [] }

theorem u4237 : Upper (D 7) (R 7) [12,257,33,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4238 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 89, targets := 128 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(3,7),(4,7)], upper := (rows 13 259 38 56 82 160 65 192 448), lower := (rows 13 259 38 56 82 160 65 128 256), losses := [] }

theorem u4238 : Upper (D 7) (R 7) [12,257,34,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4239 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,5)], upper := (rows 13 259 38 56 82 160 192 193 321), lower := (rows 13 259 38 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 20 224 224 128 256), good := (rows 28 258 126 124 126 224 224 224 256) }] }

theorem u4239 : Upper (D 7) (R 7) [12,257,34,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4240 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 89, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 13 259 38 74 49 160 80 192 448), lower := (rows 13 259 38 74 49 160 80 128 256), losses := [] }

theorem u4240 : Upper (D 7) (R 7) [12,257,34,66,33,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4240 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4241 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,5),(2,0),(3,5),(4,1)], upper := (rows 13 259 38 74 49 160 192 208 336), lower := (rows 13 259 38 74 49 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 12 16 240 240 144 272), good := (rows 12 258 110 110 496 224 224 224 256) }] }

theorem u4241 : Upper (D 7) (R 7) [12,257,34,66,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4242 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 216, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 13 259 38 74 112 33 192 144 400), lower := (rows 13 259 38 74 112 33 192 128 256), losses := [] }

theorem u4242 : Upper (D 7) (R 7) [12,257,34,66,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4243 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 13 259 38 74 112 48 192 129 385), lower := (rows 13 259 38 74 112 48 192 128 256), losses := [] }

theorem u4243 : Upper (D 7) (R 7) [12,257,34,66,96,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4243 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4244 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 259 38 74 112 160 192 145 273), lower := (rows 13 259 38 74 112 160 192 128 256), losses := [] }

theorem u4244 : Upper (D 7) (R 7) [12,257,34,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4245 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(3,7),(4,1)], upper := (rows 13 259 38 74 145 48 96 192 448), lower := (rows 13 259 38 74 145 48 96 128 256), losses := [] }

theorem u4245 : Upper (D 7) (R 7) [12,257,34,66,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4245 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4246 : Route 9 := (fun mask => (mask,id))

def c4246 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4246 : Upper (D 7) (R 7) [12,257,34,66,129,16,128] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66,129,16,128] 13 (by decide) (choices 1) [32,64] r4246 c4246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u334
  · exact u335

def b4247 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 37, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(4,1)], upper := (rows 13 259 38 74 145 96 192 176 304), lower := (rows 13 259 38 74 145 96 192 128 256), losses := [] }

theorem u4247 : Upper (D 7) (R 7) [12,257,34,66,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4248 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 89, targets := 128 },{ cop := 4, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(3,7),(4,7)], upper := (rows 13 259 38 88 49 160 66 192 448), lower := (rows 13 259 38 88 49 160 66 128 256), losses := [] }

theorem u4248 : Upper (D 7) (R 7) [12,257,34,80,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4249 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 458, targets := 32 },{ cop := 1, region := 228, targets := 1 }], pairs := [(1,5),(2,0),(3,0),(3,5)], upper := (rows 13 259 38 88 49 160 192 194 322), lower := (rows 13 259 38 88 49 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 231 231 134 262), good := (rows 492 486 486 120 120 224 224 224 256) }] }

theorem u4249 : Upper (D 7) (R 7) [12,257,34,80,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4250 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 100, targets := 1 },{ cop := 1, region := 100, targets := 128 }], pairs := [(2,0),(2,7),(3,1),(4,1)], upper := (rows 13 259 38 88 145 96 66 160 416), lower := (rows 13 259 38 88 145 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 19 104 64 237 365), good := (rows 445 401 436 504 401 488 504 128 256) }] }

theorem u4250 : Upper (D 7) (R 7) [12,257,34,80,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4251 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 13 259 38 88 145 96 96 130 386), lower := (rows 13 259 38 88 145 96 96 128 256), losses := [] }

theorem u4251 : Upper (D 7) (R 7) [12,257,34,80,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4252 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 13 259 38 88 145 96 192 162 290), lower := (rows 13 259 38 88 145 96 192 128 256), losses := [] }

theorem u4252 : Upper (D 7) (R 7) [12,257,34,80,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4253 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 228, targets := 1 }], pairs := [(1,7),(2,0),(3,7),(4,1)], upper := (rows 13 259 38 88 145 160 66 224 352), lower := (rows 13 259 38 88 145 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 249 64 200 328), good := (rows 445 305 36 504 177 160 480 160 256) },{ target := 7, region := (rows 1 3 4 24 16 32 87 0 260), good := (rows 335 323 358 88 91 32 66 0 256) }] }

theorem u4253 : Upper (D 7) (R 7) [12,257,34,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4254 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 1, region := 228, targets := 1 }], pairs := [(1,7),(2,0),(3,0),(3,1)], upper := (rows 13 259 38 88 145 160 96 194 322), lower := (rows 13 259 38 88 145 160 96 128 256), losses := [{ target := 7, region := (rows 1 19 4 8 16 32 100 0 269), good := (rows 335 259 358 346 275 96 96 0 256) }] }

theorem u4254 : Upper (D 7) (R 7) [12,257,34,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4255 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 2, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(3,7),(4,0)], upper := (rows 13 259 38 88 146 96 65 160 416), lower := (rows 13 259 38 88 146 96 65 128 256), losses := [] }

theorem u4255 : Upper (D 7) (R 7) [12,257,34,80,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4256 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 13 259 38 88 146 96 96 129 385), lower := (rows 13 259 38 88 146 96 96 128 256), losses := [] }

theorem u4256 : Upper (D 7) (R 7) [12,257,34,80,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4257 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 13 259 38 88 146 96 192 161 289), lower := (rows 13 259 38 88 146 96 192 128 256), losses := [] }

theorem u4257 : Upper (D 7) (R 7) [12,257,34,80,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4258 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 144, targets := 65 },{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(4,0),(4,6)], upper := (rows 13 259 38 88 176 96 65 130 386), lower := (rows 13 259 38 88 176 96 65 128 256), losses := [] }

theorem u4258 : Upper (D 7) (R 7) [12,257,34,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4259 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 100, targets := 129 },{ cop := 0, region := 386, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,0),(2,7)], upper := (rows 13 259 38 88 176 96 66 129 385), lower := (rows 13 259 38 88 176 96 66 128 256), losses := [] }

theorem u4259 : Upper (D 7) (R 7) [12,257,34,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4259
end Delivery.IrregularNine14.P07
