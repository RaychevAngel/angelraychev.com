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

def b3300 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 456, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 21 328 82 160 96 130 386), lower := (rows 13 35 21 328 82 160 96 128 256), losses := [] }

theorem u3300 : Upper (D 7) (R 7) [12,33,17,320,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3301 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(2,5),(3,0),(4,0)], upper := (rows 13 35 21 328 82 160 192 162 290), lower := (rows 13 35 21 328 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 18 0 224 128 256), good := (rows 13 87 21 328 86 192 192 192 256) }] }

theorem u3301 : Upper (D 7) (R 7) [12,33,17,320,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3302 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 35 22 73 336 160 66 160 416), lower := (rows 13 35 22 73 336 160 66 128 256), losses := [] }

theorem u3302 : Upper (D 7) (R 7) [12,33,18,65,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3303 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,6),(2,0),(3,1),(4,0)], upper := (rows 13 35 22 73 336 160 96 130 386), lower := (rows 13 35 22 73 336 160 96 128 256), losses := [] }

theorem u3303 : Upper (D 7) (R 7) [12,33,18,65,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3304 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,1),(1,6),(2,0),(4,0)], upper := (rows 13 35 22 73 336 160 192 162 290), lower := (rows 13 35 22 73 336 160 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 10 16 224 224 128 256), good := (rows 13 105 29 105 368 224 224 224 256) }] }

theorem u3304 : Upper (D 7) (R 7) [12,33,18,65,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3305 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 149, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 35 22 74 145 288 96 192 448), lower := (rows 13 35 22 74 145 288 96 128 256), losses := [] }

theorem u3305 : Upper (D 7) (R 7) [12,33,18,66,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3305 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3306 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 200, targets := 1 }], pairs := [(0,5),(3,0),(4,1)], upper := (rows 13 35 22 74 145 288 192 224 352), lower := (rows 13 35 22 74 145 288 192 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 16 0 208 128 256), good := (rows 13 3 95 74 209 256 192 192 256) }] }

theorem u3306 : Upper (D 7) (R 7) [12,33,18,66,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3306 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3307 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5)], upper := (rows 13 35 22 74 208 288 65 160 416), lower := (rows 13 35 22 74 208 288 65 128 256), losses := [] }

theorem u3307 : Upper (D 7) (R 7) [12,33,18,66,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3307 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3308 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 35 22 74 208 288 96 129 385), lower := (rows 13 35 22 74 208 288 96 128 256), losses := [] }

theorem u3308 : Upper (D 7) (R 7) [12,33,18,66,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3308 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3309 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 35 22 74 208 288 192 161 289), lower := (rows 13 35 22 74 208 288 192 128 256), losses := [] }

theorem u3309 : Upper (D 7) (R 7) [12,33,18,66,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3309 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3310 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,5),(4,1),(4,5)], upper := (rows 13 35 22 74 273 160 96 192 448), lower := (rows 13 35 22 74 273 160 96 128 256), losses := [] }

theorem u3310 : Upper (D 7) (R 7) [12,33,18,66,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3311 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 1, region := 200, targets := 1 }], pairs := [(0,5),(3,0),(3,5),(4,1)], upper := (rows 13 35 22 74 273 160 192 224 352), lower := (rows 13 35 22 74 273 160 192 128 256), losses := [{ target := 5, region := (rows 5 2 4 10 16 0 224 128 256), good := (rows 13 75 31 74 273 192 192 192 256) }] }

theorem u3311 : Upper (D 7) (R 7) [12,33,18,66,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3312 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 74 304 160 65 192 448), lower := (rows 13 35 22 74 304 160 65 128 256), losses := [] }

theorem u3312 : Upper (D 7) (R 7) [12,33,18,66,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3313 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(3,0),(3,5),(4,1)], upper := (rows 13 35 22 74 304 160 192 193 321), lower := (rows 13 35 22 74 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 12 106 30 106 368 224 224 224 256) }] }

theorem u3313 : Upper (D 7) (R 7) [12,33,18,66,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3314 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 35 22 74 336 160 65 160 416), lower := (rows 13 35 22 74 336 160 65 128 256), losses := [] }

theorem u3314 : Upper (D 7) (R 7) [12,33,18,66,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3315 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 35 22 74 336 160 96 129 385), lower := (rows 13 35 22 74 336 160 96 128 256), losses := [] }

theorem u3315 : Upper (D 7) (R 7) [12,33,18,66,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3316 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 162, targets := 64 }], pairs := [(0,5),(1,6),(3,0),(4,1)], upper := (rows 13 35 22 74 336 160 192 161 289), lower := (rows 13 35 22 74 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 12 106 30 106 368 224 224 224 256) },{ target := 5, region := (rows 5 2 4 10 16 0 224 128 256), good := (rows 13 75 31 74 336 192 192 192 256) }] }

theorem u3316 : Upper (D 7) (R 7) [12,33,18,66,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3317 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 35 22 74 400 160 65 224 352), lower := (rows 13 35 22 74 400 160 65 128 256), losses := [] }

theorem u3317 : Upper (D 7) (R 7) [12,33,18,66,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3318 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,5),(4,1),(4,5)], upper := (rows 13 35 22 74 400 160 96 193 321), lower := (rows 13 35 22 74 400 160 96 128 256), losses := [] }

theorem u3318 : Upper (D 7) (R 7) [12,33,18,66,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3319 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 6, region := 168, targets := 3 }], pairs := [(2,5),(3,0),(3,1),(4,5)], upper := (rows 13 35 22 104 273 160 66 192 448), lower := (rows 13 35 22 104 273 160 66 128 256), losses := [] }

theorem u3319 : Upper (D 7) (R 7) [12,33,18,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3320 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 104 273 160 192 194 322), lower := (rows 13 35 22 104 273 160 192 128 256), losses := [] }

theorem u3320 : Upper (D 7) (R 7) [12,33,18,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3321 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,6),(2,5),(3,1),(4,5)], upper := (rows 13 35 22 104 336 160 65 130 386), lower := (rows 13 35 22 104 336 160 65 128 256), losses := [] }

theorem u3321 : Upper (D 7) (R 7) [12,33,18,96,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3322 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 1, region := 468, targets := 32 }], pairs := [(2,5),(3,0),(3,7),(4,5)], upper := (rows 13 35 22 104 336 160 66 129 385), lower := (rows 13 35 22 104 336 160 66 128 256), losses := [] }

theorem u3322 : Upper (D 7) (R 7) [12,33,18,96,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3323 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 104 336 160 192 131 259), lower := (rows 13 35 22 104 336 160 192 128 256), losses := [] }

theorem u3323 : Upper (D 7) (R 7) [12,33,18,96,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3324 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(2,6),(2,7),(4,7)], upper := (rows 13 35 22 200 336 160 65 162 290), lower := (rows 13 35 22 200 336 160 65 128 256), losses := [{ target := 6, region := (rows 1 67 20 8 16 255 0 223 351), good := (rows 431 419 438 426 438 160 419 160 256) }] }

theorem u3324 : Upper (D 7) (R 7) [12,33,18,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3325 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(2,7),(3,1),(4,7)], upper := (rows 13 35 22 200 336 160 66 161 289), lower := (rows 13 35 22 200 336 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 80 239 64 131 259), good := (rows 429 417 436 248 376 160 504 160 256) }] }

theorem u3325 : Upper (D 7) (R 7) [12,33,18,192,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3326 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 340, targets := 128 },{ cop := 5, region := 72, targets := 3 }], pairs := [(2,7),(3,0),(3,1),(4,7)], upper := (rows 13 35 22 200 336 160 96 131 259), lower := (rows 13 35 22 200 336 160 96 128 256), losses := [] }

theorem u3326 : Upper (D 7) (R 7) [12,33,18,192,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3327 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 456, targets := 1 }], pairs := [(2,7),(3,0),(4,1),(4,7)], upper := (rows 13 35 22 266 81 160 96 192 448), lower := (rows 13 35 22 266 81 160 96 128 256), losses := [] }

theorem u3327 : Upper (D 7) (R 7) [12,33,18,258,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3328 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 1, region := 456, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,1)], upper := (rows 13 35 22 266 81 160 192 224 352), lower := (rows 13 35 22 266 81 160 192 128 256), losses := [{ target := 5, region := (rows 9 2 14 8 18 0 224 128 256), good := (rows 13 87 22 287 81 192 192 192 256) }] }

theorem u3328 : Upper (D 7) (R 7) [12,33,18,258,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3329 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,7),(3,5),(4,7)], upper := (rows 13 35 22 266 112 160 65 192 448), lower := (rows 13 35 22 266 112 160 65 128 256), losses := [] }

theorem u3329 : Upper (D 7) (R 7) [12,33,18,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3330 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 266 112 160 192 193 321), lower := (rows 13 35 22 266 112 160 192 128 256), losses := [] }

theorem u3330 : Upper (D 7) (R 7) [12,33,18,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3331 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 392, targets := 65 },{ cop := 5, region := 144, targets := 3 }], pairs := [(3,0),(3,6),(4,0),(4,1)], upper := (rows 13 35 22 266 208 96 65 160 416), lower := (rows 13 35 22 266 208 96 65 128 256), losses := [] }

theorem u3331 : Upper (D 7) (R 7) [12,33,18,258,192,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3332 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5),(3,6)], upper := (rows 13 35 22 266 208 96 96 129 385), lower := (rows 13 35 22 266 208 96 96 128 256), losses := [] }

theorem u3332 : Upper (D 7) (R 7) [12,33,18,258,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3333 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 266 208 96 192 161 289), lower := (rows 13 35 22 266 208 96 192 128 256), losses := [] }

theorem u3333 : Upper (D 7) (R 7) [12,33,18,258,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3334 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 296 81 160 66 192 448), lower := (rows 13 35 22 296 81 160 66 128 256), losses := [] }

theorem u3334 : Upper (D 7) (R 7) [12,33,18,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3335 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 212, targets := 32 },{ cop := 1, region := 456, targets := 1 }], pairs := [(2,5),(3,0),(4,1),(4,5)], upper := (rows 13 35 22 296 81 160 192 194 322), lower := (rows 13 35 22 296 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 224 224 128 256), good := (rows 13 113 20 360 113 224 224 224 256) }] }

theorem u3335 : Upper (D 7) (R 7) [12,33,18,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3336 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 84, targets := 160 }], pairs := [(2,5),(2,7),(4,5),(4,7)], upper := (rows 13 35 22 328 81 160 66 160 416), lower := (rows 13 35 22 328 81 160 66 128 256), losses := [] }

theorem u3336 : Upper (D 7) (R 7) [12,33,18,320,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3337 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(2,7),(4,7)], upper := (rows 13 35 22 328 81 160 96 130 386), lower := (rows 13 35 22 328 81 160 96 128 256), losses := [] }

theorem u3337 : Upper (D 7) (R 7) [12,33,18,320,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3338 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 1, region := 456, targets := 1 }], pairs := [(1,6),(2,6),(3,0),(4,1)], upper := (rows 13 35 22 328 81 160 192 162 290), lower := (rows 13 35 22 328 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 18 224 224 128 256), good := (rows 13 113 20 360 113 224 224 224 256) }] }

theorem u3338 : Upper (D 7) (R 7) [12,33,18,320,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3339 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 84, targets := 128 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,7),(3,5),(4,7)], upper := (rows 13 35 22 328 112 160 65 130 386), lower := (rows 13 35 22 328 112 160 65 128 256), losses := [] }

theorem u3339 : Upper (D 7) (R 7) [12,33,18,320,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3340 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 84, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 13 35 22 328 112 160 66 129 385), lower := (rows 13 35 22 328 112 160 66 128 256), losses := [] }

theorem u3340 : Upper (D 7) (R 7) [12,33,18,320,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3341 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 328 112 160 192 131 259), lower := (rows 13 35 22 328 112 160 192 128 256), losses := [] }

theorem u3341 : Upper (D 7) (R 7) [12,33,18,320,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3342 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,7)], upper := (rows 13 35 22 328 208 160 65 162 290), lower := (rows 13 35 22 328 208 160 65 128 256), losses := [{ target := 6, region := (rows 1 67 20 8 16 255 0 223 351), good := (rows 431 419 438 426 438 160 419 160 256) },{ target := 7, region := (rows 5 2 4 14 16 32 71 0 258), good := (rows 77 363 351 328 80 32 65 0 256) }] }

theorem u3342 : Upper (D 7) (R 7) [12,33,18,320,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3343 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,1),(3,7),(4,1)], upper := (rows 13 35 22 328 208 160 66 161 289), lower := (rows 13 35 22 328 208 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 80 247 64 131 259), good := (rows 429 417 436 376 248 160 504 160 256) }] }

theorem u3343 : Upper (D 7) (R 7) [12,33,18,320,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3344 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 0, region := 162, targets := 64 },{ cop := 1, region := 328, targets := 128 }], pairs := [(1,6),(3,7),(4,0),(4,1)], upper := (rows 13 35 22 328 208 160 96 131 259), lower := (rows 13 35 22 328 208 160 96 128 256), losses := [] }

theorem u3344 : Upper (D 7) (R 7) [12,33,18,320,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3345 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 1, region := 72, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 13 35 52 74 336 160 65 130 386), lower := (rows 13 35 52 74 336 160 65 128 256), losses := [] }

theorem u3345 : Upper (D 7) (R 7) [12,33,48,66,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3346 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(3,7)], upper := (rows 13 35 52 74 336 160 66 129 385), lower := (rows 13 35 52 74 336 160 66 128 256), losses := [] }

theorem u3346 : Upper (D 7) (R 7) [12,33,48,66,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3347 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6),(2,0),(3,5),(4,5)], upper := (rows 13 35 52 74 336 160 192 131 259), lower := (rows 13 35 52 74 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 10 16 224 224 128 256), good := (rows 12 106 116 106 372 224 224 224 256) }] }

theorem u3347 : Upper (D 7) (R 7) [12,33,48,66,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3348 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 35 69 138 112 288 66 144 400), lower := (rows 13 35 69 138 112 288 66 128 256), losses := [] }

theorem u3348 : Upper (D 7) (R 7) [12,33,65,130,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3348 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3349 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 13 35 69 138 112 288 80 130 386), lower := (rows 13 35 69 138 112 288 80 128 256), losses := [] }

theorem u3349 : Upper (D 7) (R 7) [12,33,65,130,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3349 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3350 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 69, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 35 69 138 112 288 192 146 274), lower := (rows 13 35 69 138 112 288 192 128 256), losses := [] }

theorem u3350 : Upper (D 7) (R 7) [12,33,65,130,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3350 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3351 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 35 69 138 176 288 66 208 336), lower := (rows 13 35 69 138 176 288 66 128 256), losses := [] }

theorem u3351 : Upper (D 7) (R 7) [12,33,65,130,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3351 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3352 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 216, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 13 35 69 138 176 288 80 194 322), lower := (rows 13 35 69 138 176 288 80 128 256), losses := [] }

theorem u3352 : Upper (D 7) (R 7) [12,33,65,130,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3352 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3353 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 13 35 69 138 208 288 66 176 304), lower := (rows 13 35 69 138 208 288 66 128 256), losses := [] }

theorem u3353 : Upper (D 7) (R 7) [12,33,65,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3353 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3354 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 85, targets := 34 }], pairs := [(0,1),(0,5)], upper := (rows 13 35 69 138 208 288 80 162 290), lower := (rows 13 35 69 138 208 288 80 128 256), losses := [] }

theorem u3354 : Upper (D 7) (R 7) [12,33,65,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3354 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3355 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 216, targets := 1 },{ cop := 1, region := 68, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 13 35 69 138 208 288 96 146 274), lower := (rows 13 35 69 138 208 288 96 128 256), losses := [] }

theorem u3355 : Upper (D 7) (R 7) [12,33,65,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3355 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3356 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 85, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 35 69 266 82 160 80 160 416), lower := (rows 13 35 69 266 82 160 80 128 256), losses := [] }

theorem u3356 : Upper (D 7) (R 7) [12,33,65,258,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3356 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3357 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 472, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 13 35 69 266 82 160 96 144 400), lower := (rows 13 35 69 266 82 160 96 128 256), losses := [] }

theorem u3357 : Upper (D 7) (R 7) [12,33,65,258,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3358 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 472, targets := 1 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(3,0),(3,6),(4,0)], upper := (rows 13 35 69 266 82 160 192 176 304), lower := (rows 13 35 69 266 82 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 6 8 16 240 240 144 272), good := (rows 13 101 101 269 500 224 224 224 256) }] }

theorem u3358 : Upper (D 7) (R 7) [12,33,65,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3359 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 69 266 112 160 66 144 400), lower := (rows 13 35 69 266 112 160 66 128 256), losses := [] }

theorem u3359 : Upper (D 7) (R 7) [12,33,65,258,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u3359
end Delivery.IrregularNine14.P07
