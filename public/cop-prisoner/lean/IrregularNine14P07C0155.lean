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

def b9300 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 225, targets := 2 },{ cop := 2, region := 208, targets := 32 }], pairs := [(0,1),(3,0),(3,1),(4,5)], upper := (rows 37 266 7 56 82 160 192 193 321), lower := (rows 37 266 7 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 100 266 6 120 122 224 224 224 256) },{ target := 1, region := (rows 5 0 4 24 16 229 229 133 261), good := (rows 485 264 485 120 120 224 224 224 256) }] }

theorem u9300 : Upper (D 7) (R 7) [36,264,3,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9301 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 37 266 7 73 112 160 66 144 400), lower := (rows 37 266 7 73 112 160 66 128 256), losses := [] }

theorem u9301 : Upper (D 7) (R 7) [36,264,3,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9302 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 266 7 73 112 160 80 130 386), lower := (rows 37 266 7 73 112 160 80 128 256), losses := [] }

theorem u9302 : Upper (D 7) (R 7) [36,264,3,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9302 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9303 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 73 112 160 192 146 274), lower := (rows 37 266 7 73 112 160 192 128 256), losses := [] }

theorem u9303 : Upper (D 7) (R 7) [36,264,3,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9304 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 37 266 7 73 208 48 66 160 416), lower := (rows 37 266 7 73 208 48 66 128 256), losses := [] }

theorem u9304 : Upper (D 7) (R 7) [36,264,3,65,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9305 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 266 7 73 208 48 96 130 386), lower := (rows 37 266 7 73 208 48 96 128 256), losses := [] }

theorem u9305 : Upper (D 7) (R 7) [36,264,3,65,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9305 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9306 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 7 73 208 48 192 162 290), lower := (rows 37 266 7 73 208 48 192 128 256), losses := [] }

theorem u9306 : Upper (D 7) (R 7) [36,264,3,65,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9306 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9307 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 37 266 7 73 208 160 66 176 304), lower := (rows 37 266 7 73 208 160 66 128 256), losses := [] }

theorem u9307 : Upper (D 7) (R 7) [36,264,3,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9308 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 266 7 73 208 160 80 162 290), lower := (rows 37 266 7 73 208 160 80 128 256), losses := [] }

theorem u9308 : Upper (D 7) (R 7) [36,264,3,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9308 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9309 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 7 73 208 160 96 146 274), lower := (rows 37 266 7 73 208 160 96 128 256), losses := [] }

theorem u9309 : Upper (D 7) (R 7) [36,264,3,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9310 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 266 7 74 112 160 65 144 400), lower := (rows 37 266 7 74 112 160 65 128 256), losses := [] }

theorem u9310 : Upper (D 7) (R 7) [36,264,3,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9311 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 266 7 74 112 160 80 129 385), lower := (rows 37 266 7 74 112 160 80 128 256), losses := [] }

theorem u9311 : Upper (D 7) (R 7) [36,264,3,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9311 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9312 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 7 74 112 160 192 145 273), lower := (rows 37 266 7 74 112 160 192 128 256), losses := [] }

theorem u9312 : Upper (D 7) (R 7) [36,264,3,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9313 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 266 7 74 208 48 65 160 416), lower := (rows 37 266 7 74 208 48 65 128 256), losses := [] }

theorem u9313 : Upper (D 7) (R 7) [36,264,3,66,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9313 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9314 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 7, region := 112, targets := 1 }], pairs := [(0,1),(4,0),(4,1)], upper := (rows 37 266 7 74 208 48 96 129 385), lower := (rows 37 266 7 74 208 48 96 128 256), losses := [] }

theorem u9314 : Upper (D 7) (R 7) [36,264,3,66,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9314 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9315 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 7 74 208 48 192 161 289), lower := (rows 37 266 7 74 208 48 192 128 256), losses := [] }

theorem u9315 : Upper (D 7) (R 7) [36,264,3,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9315 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9316 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 37 266 7 74 208 160 65 176 304), lower := (rows 37 266 7 74 208 160 65 128 256), losses := [] }

theorem u9316 : Upper (D 7) (R 7) [36,264,3,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9317 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 266 7 74 208 160 80 161 289), lower := (rows 37 266 7 74 208 160 80 128 256), losses := [] }

theorem u9317 : Upper (D 7) (R 7) [36,264,3,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9317 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9318 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,1),(3,0),(4,0),(4,1)], upper := (rows 37 266 7 74 208 160 96 145 273), lower := (rows 37 266 7 74 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 176 176 241 128 256), good := (rows 124 266 78 74 240 240 112 240 256) }] }

theorem u9318 : Upper (D 7) (R 7) [36,264,3,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9319 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 266 7 88 145 160 66 224 352), lower := (rows 37 266 7 88 145 160 66 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 250 64 200 328), good := (rows 37 424 37 504 177 160 480 160 256) },{ target := 7, region := (rows 1 18 20 24 16 32 94 0 257), good := (rows 357 330 327 94 351 32 66 0 256) }] }

theorem u9319 : Upper (D 7) (R 7) [36,264,3,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9320 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 258, targets := 32 },{ cop := 3, region := 258, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 37 266 7 88 145 160 96 194 322), lower := (rows 37 266 7 88 145 160 96 128 256), losses := [] }

theorem u9320 : Upper (D 7) (R 7) [36,264,3,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9321 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 266 7 88 146 160 65 224 352), lower := (rows 37 266 7 88 146 160 65 128 256), losses := [] }

theorem u9321 : Upper (D 7) (R 7) [36,264,3,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9322 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 37 266 7 88 146 160 96 193 321), lower := (rows 37 266 7 88 146 160 96 128 256), losses := [] }

theorem u9322 : Upper (D 7) (R 7) [36,264,3,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9323 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 37 266 7 88 176 96 65 130 386), lower := (rows 37 266 7 88 176 96 65 128 256), losses := [] }

theorem u9323 : Upper (D 7) (R 7) [36,264,3,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9324 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 37 266 7 88 176 96 66 129 385), lower := (rows 37 266 7 88 176 96 66 128 256), losses := [] }

theorem u9324 : Upper (D 7) (R 7) [36,264,3,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9325 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 37 266 7 88 176 96 192 131 259), lower := (rows 37 266 7 88 176 96 192 128 256), losses := [] }

theorem u9325 : Upper (D 7) (R 7) [36,264,3,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9326 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 80, targets := 32 },{ cop := 2, region := 80, targets := 128 }], pairs := [(1,0),(3,0),(4,5),(4,7)], upper := (rows 37 266 7 104 81 160 66 144 400), lower := (rows 37 266 7 104 81 160 66 128 256), losses := [] }

theorem u9326 : Upper (D 7) (R 7) [36,264,3,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9327 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 37 266 7 104 81 160 80 130 386), lower := (rows 37 266 7 104 81 160 80 128 256), losses := [] }

theorem u9327 : Upper (D 7) (R 7) [36,264,3,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9327 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9328 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 7 104 81 160 192 146 274), lower := (rows 37 266 7 104 81 160 192 128 256), losses := [] }

theorem u9328 : Upper (D 7) (R 7) [36,264,3,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9329 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 266 7 104 82 160 65 144 400), lower := (rows 37 266 7 104 82 160 65 128 256), losses := [] }

theorem u9329 : Upper (D 7) (R 7) [36,264,3,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9330 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 266 7 104 82 160 80 129 385), lower := (rows 37 266 7 104 82 160 80 128 256), losses := [] }

theorem u9330 : Upper (D 7) (R 7) [36,264,3,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9330 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9331 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 7 104 82 160 192 145 273), lower := (rows 37 266 7 104 82 160 192 128 256), losses := [] }

theorem u9331 : Upper (D 7) (R 7) [36,264,3,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9332 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(1,7),(3,0),(4,5)], upper := (rows 37 266 7 104 145 160 66 208 336), lower := (rows 37 266 7 104 145 160 66 128 256), losses := [{ target := 7, region := (rows 1 18 20 9 16 32 86 0 272), good := (rows 109 330 79 104 351 32 66 0 256) }] }

theorem u9332 : Upper (D 7) (R 7) [36,264,3,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9333 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 7 104 145 160 80 194 322), lower := (rows 37 266 7 104 145 160 80 128 256), losses := [] }

theorem u9333 : Upper (D 7) (R 7) [36,264,3,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9333 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9334 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 266 7 104 146 160 65 208 336), lower := (rows 37 266 7 104 146 160 65 128 256), losses := [] }

theorem u9334 : Upper (D 7) (R 7) [36,264,3,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9335 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 7 104 146 160 80 193 321), lower := (rows 37 266 7 104 146 160 80 128 256), losses := [] }

theorem u9335 : Upper (D 7) (R 7) [36,264,3,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9335 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9336 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 266 7 104 208 160 65 146 274), lower := (rows 37 266 7 104 208 160 65 128 256), losses := [] }

theorem u9336 : Upper (D 7) (R 7) [36,264,3,96,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9337 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 2, region := 208, targets := 32 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 37 266 7 104 208 160 66 145 273), lower := (rows 37 266 7 104 208 160 66 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 16 32 70 0 256), good := (rows 109 330 79 104 80 32 66 0 256) }] }

theorem u9337 : Upper (D 7) (R 7) [36,264,3,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9338 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 37 266 7 104 208 160 80 131 259), lower := (rows 37 266 7 104 208 160 80 128 256), losses := [] }

theorem u9338 : Upper (D 7) (R 7) [36,264,3,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9338 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9339 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 266 7 200 81 48 66 160 416), lower := (rows 37 266 7 200 81 48 66 128 256), losses := [] }

theorem u9339 : Upper (D 7) (R 7) [36,264,3,192,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9339 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9340 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 266 7 200 81 48 96 130 386), lower := (rows 37 266 7 200 81 48 96 128 256), losses := [] }

theorem u9340 : Upper (D 7) (R 7) [36,264,3,192,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9341 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 7 200 81 48 192 162 290), lower := (rows 37 266 7 200 81 48 192 128 256), losses := [] }

theorem u9341 : Upper (D 7) (R 7) [36,264,3,192,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9341 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9342 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 37 266 7 200 82 160 65 176 304), lower := (rows 37 266 7 200 82 160 65 128 256), losses := [] }

theorem u9342 : Upper (D 7) (R 7) [36,264,3,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9343 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 266 7 200 82 160 80 161 289), lower := (rows 37 266 7 200 82 160 80 128 256), losses := [] }

theorem u9343 : Upper (D 7) (R 7) [36,264,3,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9343 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9344 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 165, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 37 266 7 200 82 160 96 145 273), lower := (rows 37 266 7 200 82 160 96 128 256), losses := [] }

theorem u9344 : Upper (D 7) (R 7) [36,264,3,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9345 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 85, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 266 21 42 82 160 65 192 448), lower := (rows 37 266 21 42 82 160 65 128 256), losses := [] }

theorem u9345 : Upper (D 7) (R 7) [36,264,17,34,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9346 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(2,1),(3,0),(4,0)], upper := (rows 37 266 21 42 82 160 192 193 321), lower := (rows 37 266 21 42 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 224 224 128 256), good := (rows 100 282 28 122 122 224 224 224 256) }] }

theorem u9346 : Upper (D 7) (R 7) [36,264,17,34,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9347 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 266 21 73 146 96 66 160 416), lower := (rows 37 266 21 73 146 96 66 128 256), losses := [] }

theorem u9347 : Upper (D 7) (R 7) [36,264,17,65,130,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9348 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6)], upper := (rows 37 266 21 73 146 96 96 130 386), lower := (rows 37 266 21 73 146 96 96 128 256), losses := [] }

theorem u9348 : Upper (D 7) (R 7) [36,264,17,65,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9349 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 3, region := 290, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 266 21 73 146 96 192 162 290), lower := (rows 37 266 21 73 146 96 192 128 256), losses := [] }

theorem u9349 : Upper (D 7) (R 7) [36,264,17,65,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9350 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,1),(4,0)], upper := (rows 37 266 21 73 208 34 66 160 416), lower := (rows 37 266 21 73 208 34 66 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 32 64 161 289), good := (rows 421 284 405 477 208 416 64 128 256) }] }

theorem u9350 : Upper (D 7) (R 7) [36,264,17,65,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9351 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 21 73 208 34 96 130 386), lower := (rows 37 266 21 73 208 34 96 128 256), losses := [] }

theorem u9351 : Upper (D 7) (R 7) [36,264,17,65,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9352 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 21 73 208 34 192 162 290), lower := (rows 37 266 21 73 208 34 192 128 256), losses := [] }

theorem u9352 : Upper (D 7) (R 7) [36,264,17,65,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9353 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 5, region := 394, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 37 266 21 74 146 96 65 160 416), lower := (rows 37 266 21 74 146 96 65 128 256), losses := [] }

theorem u9353 : Upper (D 7) (R 7) [36,264,17,66,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9354 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 266 21 74 146 96 96 129 385), lower := (rows 37 266 21 74 146 96 96 128 256), losses := [] }

theorem u9354 : Upper (D 7) (R 7) [36,264,17,66,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9355 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 101, targets := 2 },{ cop := 4, region := 72, targets := 1 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,1),(2,1),(3,0),(3,5)], upper := (rows 37 266 21 74 146 96 192 161 289), lower := (rows 37 266 21 74 146 96 192 128 256), losses := [] }

theorem u9355 : Upper (D 7) (R 7) [36,264,17,66,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9356 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 21 74 208 34 65 160 416), lower := (rows 37 266 21 74 208 34 65 128 256), losses := [] }

theorem u9356 : Upper (D 7) (R 7) [36,264,17,66,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9357 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 266 21 74 208 34 96 129 385), lower := (rows 37 266 21 74 208 34 96 128 256), losses := [] }

theorem u9357 : Upper (D 7) (R 7) [36,264,17,66,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9358 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 21 74 208 34 192 161 289), lower := (rows 37 266 21 74 208 34 192 128 256), losses := [] }

theorem u9358 : Upper (D 7) (R 7) [36,264,17,66,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9359 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 37 266 21 104 82 160 65 130 386), lower := (rows 37 266 21 104 82 160 65 128 256), losses := [] }

theorem u9359 : Upper (D 7) (R 7) [36,264,17,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9359
end Delivery.IrregularNine14.P07
