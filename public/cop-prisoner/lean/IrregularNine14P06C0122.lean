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

def b7320 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 3, region := 130, targets := 32 },{ cop := 3, region := 130, targets := 64 }], pairs := [(0,2),(1,5),(1,6)], upper := (rows 35 138 84 13 304 96 66 133 261), lower := (rows 35 138 84 13 304 96 66 128 256), losses := [] }

theorem u7320 : Upper (D 6) (R 6) [34,136,80,5,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7321 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 84 13 304 96 68 131 259), lower := (rows 35 138 84 13 304 96 68 128 256), losses := [] }

theorem u7321 : Upper (D 6) (R 6) [34,136,80,5,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7322 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 92, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 138 84 73 22 288 65 164 292), lower := (rows 35 138 84 73 22 288 65 128 256), losses := [] }

theorem u7322 : Upper (D 6) (R 6) [34,136,80,65,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7322 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7323 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 35 138 84 73 22 288 68 161 289), lower := (rows 35 138 84 73 22 288 68 128 256), losses := [] }

theorem u7323 : Upper (D 6) (R 6) [34,136,80,65,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7323 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7324 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 138 84 73 22 288 96 133 261), lower := (rows 35 138 84 73 22 288 96 128 256), losses := [] }

theorem u7324 : Upper (D 6) (R 6) [34,136,80,65,6,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7324 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7325 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 92, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 84 73 52 288 65 134 262), lower := (rows 35 138 84 73 52 288 65 128 256), losses := [] }

theorem u7325 : Upper (D 6) (R 6) [34,136,80,65,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7325 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7326 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 84 73 52 288 66 133 261), lower := (rows 35 138 84 73 52 288 66 128 256), losses := [] }

theorem u7326 : Upper (D 6) (R 6) [34,136,80,65,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7326 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7327 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 419, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 138 84 73 52 288 68 131 259), lower := (rows 35 138 84 73 52 288 68 128 256), losses := [] }

theorem u7327 : Upper (D 6) (R 6) [34,136,80,65,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7327 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7328 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 35 138 84 73 273 36 66 164 292), lower := (rows 35 138 84 73 273 36 66 128 256), losses := [] }

theorem u7328 : Upper (D 6) (R 6) [34,136,80,65,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7329 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 35 138 84 73 273 36 68 162 290), lower := (rows 35 138 84 73 273 36 68 128 256), losses := [] }

theorem u7329 : Upper (D 6) (R 6) [34,136,80,65,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7330 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 84 73 273 36 96 134 262), lower := (rows 35 138 84 73 273 36 96 128 256), losses := [] }

theorem u7330 : Upper (D 6) (R 6) [34,136,80,65,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7331 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 84 73 274 36 65 164 292), lower := (rows 35 138 84 73 274 36 65 128 256), losses := [] }

theorem u7331 : Upper (D 6) (R 6) [34,136,80,65,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7332 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 272, targets := 68 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 35 138 84 73 274 36 68 161 289), lower := (rows 35 138 84 73 274 36 68 128 256), losses := [] }

theorem u7332 : Upper (D 6) (R 6) [34,136,80,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7333 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 84 73 274 36 96 133 261), lower := (rows 35 138 84 73 274 36 96 128 256), losses := [] }

theorem u7333 : Upper (D 6) (R 6) [34,136,80,65,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7334 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 84 73 304 36 65 134 262), lower := (rows 35 138 84 73 304 36 65 128 256), losses := [] }

theorem u7334 : Upper (D 6) (R 6) [34,136,80,65,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7334 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7335 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 35 138 84 73 304 36 66 133 261), lower := (rows 35 138 84 73 304 36 66 128 256), losses := [] }

theorem u7335 : Upper (D 6) (R 6) [34,136,80,65,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7336 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 84 73 304 36 68 131 259), lower := (rows 35 138 84 73 304 36 68 128 256), losses := [] }

theorem u7336 : Upper (D 6) (R 6) [34,136,80,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7337 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 84 74 273 36 65 164 292), lower := (rows 35 138 84 74 273 36 65 128 256), losses := [] }

theorem u7337 : Upper (D 6) (R 6) [34,136,80,66,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7338 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 272, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 84 74 273 36 68 161 289), lower := (rows 35 138 84 74 273 36 68 128 256), losses := [] }

theorem u7338 : Upper (D 6) (R 6) [34,136,80,66,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7339 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 35 138 84 74 273 36 96 133 261), lower := (rows 35 138 84 74 273 36 96 128 256), losses := [] }

theorem u7339 : Upper (D 6) (R 6) [34,136,80,66,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7340 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 84 74 304 36 65 133 261), lower := (rows 35 138 84 74 304 36 65 128 256), losses := [] }

theorem u7340 : Upper (D 6) (R 6) [34,136,80,66,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7341 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 138 84 74 304 36 68 129 257), lower := (rows 35 138 84 74 304 36 68 128 256), losses := [] }

theorem u7341 : Upper (D 6) (R 6) [34,136,80,66,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7342 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 265 21 96 66 164 292), lower := (rows 35 138 84 265 21 96 66 128 256), losses := [] }

theorem u7342 : Upper (D 6) (R 6) [34,136,80,257,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7343 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 265 21 96 68 162 290), lower := (rows 35 138 84 265 21 96 68 128 256), losses := [] }

theorem u7343 : Upper (D 6) (R 6) [34,136,80,257,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7344 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 138 84 265 21 96 96 134 262), lower := (rows 35 138 84 265 21 96 96 128 256), losses := [] }

theorem u7344 : Upper (D 6) (R 6) [34,136,80,257,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7345 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 265 22 96 65 164 292), lower := (rows 35 138 84 265 22 96 65 128 256), losses := [] }

theorem u7345 : Upper (D 6) (R 6) [34,136,80,257,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 265 22 96 68 161 289), lower := (rows 35 138 84 265 22 96 68 128 256), losses := [] }

theorem u7346 : Upper (D 6) (R 6) [34,136,80,257,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7347 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 265 22 96 96 133 261), lower := (rows 35 138 84 265 22 96 96 128 256), losses := [] }

theorem u7347 : Upper (D 6) (R 6) [34,136,80,257,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7348 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 0, region := 84, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 84 266 21 96 65 164 292), lower := (rows 35 138 84 266 21 96 65 128 256), losses := [] }

theorem u7348 : Upper (D 6) (R 6) [34,136,80,258,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7349 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 266 21 96 68 161 289), lower := (rows 35 138 84 266 21 96 68 128 256), losses := [] }

theorem u7349 : Upper (D 6) (R 6) [34,136,80,258,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7350 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 394, targets := 96 }], pairs := [(1,5),(1,6),(3,5)], upper := (rows 35 138 84 266 21 96 96 133 261), lower := (rows 35 138 84 266 21 96 96 128 256), losses := [] }

theorem u7350 : Upper (D 6) (R 6) [34,136,80,258,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7351 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 268 22 96 65 161 289), lower := (rows 35 138 84 268 22 96 65 128 256), losses := [] }

theorem u7351 : Upper (D 6) (R 6) [34,136,80,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7352 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 268 22 96 96 129 257), lower := (rows 35 138 84 268 22 96 96 128 256), losses := [] }

theorem u7352 : Upper (D 6) (R 6) [34,136,80,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7353 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 0, region := 84, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 84 296 21 96 65 134 262), lower := (rows 35 138 84 296 21 96 65 128 256), losses := [] }

theorem u7353 : Upper (D 6) (R 6) [34,136,80,288,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7354 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 296 21 96 66 133 261), lower := (rows 35 138 84 296 21 96 66 128 256), losses := [] }

theorem u7354 : Upper (D 6) (R 6) [34,136,80,288,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7355 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 296 21 96 68 131 259), lower := (rows 35 138 84 296 21 96 68 128 256), losses := [] }

theorem u7355 : Upper (D 6) (R 6) [34,136,80,288,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7356 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 328 21 33 66 164 292), lower := (rows 35 138 84 328 21 33 66 128 256), losses := [] }

theorem u7356 : Upper (D 6) (R 6) [34,136,80,320,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7357 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 328 21 33 68 162 290), lower := (rows 35 138 84 328 21 33 68 128 256), losses := [] }

theorem u7357 : Upper (D 6) (R 6) [34,136,80,320,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7358 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 84 328 21 33 96 134 262), lower := (rows 35 138 84 328 21 33 96 128 256), losses := [] }

theorem u7358 : Upper (D 6) (R 6) [34,136,80,320,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7359 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 84 328 22 33 65 164 292), lower := (rows 35 138 84 328 22 33 65 128 256), losses := [] }

theorem u7359 : Upper (D 6) (R 6) [34,136,80,320,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7360 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 35 138 84 328 22 33 68 161 289), lower := (rows 35 138 84 328 22 33 68 128 256), losses := [] }

theorem u7360 : Upper (D 6) (R 6) [34,136,80,320,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7361 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 328 22 33 96 133 261), lower := (rows 35 138 84 328 22 33 96 128 256), losses := [] }

theorem u7361 : Upper (D 6) (R 6) [34,136,80,320,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7362 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 84 328 52 33 65 134 262), lower := (rows 35 138 84 328 52 33 65 128 256), losses := [] }

theorem u7362 : Upper (D 6) (R 6) [34,136,80,320,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7363 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 84 328 52 33 66 133 261), lower := (rows 35 138 84 328 52 33 66 128 256), losses := [] }

theorem u7363 : Upper (D 6) (R 6) [34,136,80,320,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7364 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 35 138 84 328 52 33 68 131 259), lower := (rows 35 138 84 328 52 33 68 128 256), losses := [] }

theorem u7364 : Upper (D 6) (R 6) [34,136,80,320,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7365 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 292, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 138 100 25 22 288 65 196 324), lower := (rows 35 138 100 25 22 288 65 128 256), losses := [] }

theorem u7365 : Upper (D 6) (R 6) [34,136,96,17,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7365 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7366 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 100 25 22 288 68 193 321), lower := (rows 35 138 100 25 22 288 68 128 256), losses := [] }

theorem u7366 : Upper (D 6) (R 6) [34,136,96,17,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7366 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7367 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 100 25 82 36 65 388 260), lower := (rows 35 138 100 25 82 36 65 128 256), losses := [] }

theorem u7367 : Upper (D 6) (R 6) [34,136,96,17,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7368 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 25 82 36 68 385 257), lower := (rows 35 138 100 25 82 36 68 128 256), losses := [] }

theorem u7368 : Upper (D 6) (R 6) [34,136,96,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7369 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 138 100 25 82 36 320 133 261), lower := (rows 35 138 100 25 82 36 320 128 256), losses := [] }

theorem u7369 : Upper (D 6) (R 6) [34,136,96,17,66,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7369 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7370 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 138 100 25 82 288 65 132 260), lower := (rows 35 138 100 25 82 288 65 128 256), losses := [] }

theorem u7370 : Upper (D 6) (R 6) [34,136,96,17,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7370 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7371 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 100 25 82 288 68 133 261), lower := (rows 35 138 100 25 82 288 68 128 256), losses := [] }

theorem u7371 : Upper (D 6) (R 6) [34,136,96,17,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7371 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7372 : Route 9 := (fun mask => (mask,id))

def c7372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7372 : Upper (D 6) (R 6) [34,136,96,17,258,4,1] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,258,4,1] 13 (by decide) (choices 1) [4,64] r7372 c7372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u567
  · exact u568

def b7373 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 25 274 36 68 193 321), lower := (rows 35 138 100 25 274 36 68 128 256), losses := [] }

theorem u7373 : Upper (D 6) (R 6) [34,136,96,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7374 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 36, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 35 138 100 25 336 36 65 134 262), lower := (rows 35 138 100 25 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 10 84 8 16 124 64 136 264), good := (rows 34 426 100 446 372 36 100 128 256) }] }

theorem u7374 : Upper (D 6) (R 6) [34,136,96,17,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7375 : Route 9 := (fun mask => (mask,id))

def c7375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7375 : Upper (D 6) (R 6) [34,136,96,17,320,4,2] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,320,4,2] 13 (by decide) (choices 1) [1,4] r7375 c7375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u569
  · exact u570

def b7376 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 100 25 336 36 68 131 259), lower := (rows 35 138 100 25 336 36 68 128 256), losses := [] }

theorem u7376 : Upper (D 6) (R 6) [34,136,96,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7377 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 138 100 73 22 288 65 148 276), lower := (rows 35 138 100 73 22 288 65 128 256), losses := [] }

theorem u7377 : Upper (D 6) (R 6) [34,136,96,65,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7377 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7378 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 138 100 73 22 288 68 145 273), lower := (rows 35 138 100 73 22 288 68 128 256), losses := [] }

theorem u7378 : Upper (D 6) (R 6) [34,136,96,65,6,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7378 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7379 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 1 }], pairs := [(2,0)], upper := (rows 35 138 100 73 22 288 80 133 261), lower := (rows 35 138 100 73 22 288 80 128 256), losses := [] }

theorem u7379 : Upper (D 6) (R 6) [34,136,96,65,6,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7379 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7379
end Delivery.IrregularNine14.P06
