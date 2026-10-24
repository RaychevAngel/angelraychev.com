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

def b4320 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 109, targets := 128 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 13 274 38 104 208 33 66 129 385), lower := (rows 13 274 38 104 208 33 66 128 256), losses := [] }

theorem u4320 : Upper (D 7) (R 7) [12,272,34,96,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4321 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 38 104 208 33 192 131 259), lower := (rows 13 274 38 104 208 33 192 128 256), losses := [] }

theorem u4321 : Upper (D 7) (R 7) [12,272,34,96,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4322 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 201, targets := 2 },{ cop := 4, region := 100, targets := 128 },{ cop := 5, region := 136, targets := 1 }], pairs := [(0,1),(2,7),(3,0),(3,1)], upper := (rows 13 274 38 200 19 96 65 160 416), lower := (rows 13 274 38 200 19 96 65 128 256), losses := [] }

theorem u4322 : Upper (D 7) (R 7) [12,272,34,192,3,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4323 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 402, targets := 96 }], pairs := [(1,5),(1,6),(4,5),(4,6)], upper := (rows 13 274 38 200 19 96 96 129 385), lower := (rows 13 274 38 200 19 96 96 128 256), losses := [] }

theorem u4323 : Upper (D 7) (R 7) [12,272,34,192,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 38 200 19 96 192 161 289), lower := (rows 13 274 38 200 19 96 192 128 256), losses := [] }

theorem u4324 : Upper (D 7) (R 7) [12,272,34,192,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 274 38 200 81 160 65 162 290), lower := (rows 13 274 38 200 81 160 65 128 256), losses := [] }

theorem u4325 : Upper (D 7) (R 7) [12,272,34,192,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4326 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 4, region := 168, targets := 2 }], pairs := [(1,6),(2,6),(3,1),(4,5)], upper := (rows 13 274 38 200 81 160 66 161 289), lower := (rows 13 274 38 200 81 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 128 256), good := (rows 93 338 70 200 81 128 66 128 256) }] }

theorem u4326 : Upper (D 7) (R 7) [12,272,34,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4327 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 394, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(2,6),(3,5)], upper := (rows 13 274 38 200 81 160 96 131 259), lower := (rows 13 274 38 200 81 160 96 128 256), losses := [] }

theorem u4327 : Upper (D 7) (R 7) [12,272,34,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4328 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(1,6),(3,1),(4,5)], upper := (rows 13 274 38 200 82 33 65 160 416), lower := (rows 13 274 38 200 82 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 97 128 256), good := (rows 93 274 86 200 82 65 65 128 256) },{ target := 6, region := (rows 1 18 20 8 16 97 0 253 381), good := (rows 429 406 422 424 438 417 417 128 256) }] }

theorem u4328 : Upper (D 7) (R 7) [12,272,34,192,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 129 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(3,1),(4,0),(4,7)], upper := (rows 13 274 38 200 82 33 96 129 385), lower := (rows 13 274 38 200 82 33 96 128 256), losses := [] }

theorem u4329 : Upper (D 7) (R 7) [12,272,34,192,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4330 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 38 200 82 33 192 161 289), lower := (rows 13 274 38 200 82 33 192 128 256), losses := [] }

theorem u4330 : Upper (D 7) (R 7) [12,272,34,192,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4331 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(3,1)], upper := (rows 13 274 38 200 82 160 65 161 289), lower := (rows 13 274 38 200 82 160 65 128 256), losses := [{ target := 6, region := (rows 1 18 22 8 16 249 0 193 321), good := (rows 429 310 38 424 438 160 417 160 256) }] }

theorem u4331 : Upper (D 7) (R 7) [12,272,34,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 80, targets := 129 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(3,1),(4,0),(4,7)], upper := (rows 13 274 38 200 82 160 96 129 257), lower := (rows 13 274 38 200 82 160 96 128 256), losses := [] }

theorem u4332 : Upper (D 7) (R 7) [12,272,34,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 1 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 274 38 200 112 33 65 130 386), lower := (rows 13 274 38 200 112 33 65 128 256), losses := [] }

theorem u4333 : Upper (D 7) (R 7) [12,272,34,192,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4334 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 129 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(3,5),(4,0),(4,7)], upper := (rows 13 274 38 200 112 33 66 129 385), lower := (rows 13 274 38 200 112 33 66 128 256), losses := [] }

theorem u4334 : Upper (D 7) (R 7) [12,272,34,192,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4335 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 38 200 112 33 192 131 259), lower := (rows 13 274 38 200 112 33 192 128 256), losses := [] }

theorem u4335 : Upper (D 7) (R 7) [12,272,34,192,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4336 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 173, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 274 100 168 19 33 66 192 448), lower := (rows 13 274 100 168 19 33 66 128 256), losses := [] }

theorem u4336 : Upper (D 7) (R 7) [12,272,96,160,3,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4337 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 274 100 168 19 33 192 194 322), lower := (rows 13 274 100 168 19 33 192 128 256), losses := [] }

theorem u4337 : Upper (D 7) (R 7) [12,272,96,160,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4338 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 100 168 82 33 65 130 386), lower := (rows 13 274 100 168 82 33 65 128 256), losses := [] }

theorem u4338 : Upper (D 7) (R 7) [12,272,96,160,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4339 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 82, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(4,0)], upper := (rows 13 274 100 168 82 33 66 129 385), lower := (rows 13 274 100 168 82 33 66 128 256), losses := [] }

theorem u4339 : Upper (D 7) (R 7) [12,272,96,160,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4340 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 274 100 168 82 33 192 131 259), lower := (rows 13 274 100 168 82 33 192 128 256), losses := [] }

theorem u4340 : Upper (D 7) (R 7) [12,272,96,160,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4341 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 13 274 100 168 208 34 65 131 259), lower := (rows 13 274 100 168 208 34 65 128 256), losses := [] }

theorem u4341 : Upper (D 7) (R 7) [12,272,96,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4342 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 153, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(3,1),(4,1)], upper := (rows 13 274 100 168 208 34 66 129 257), lower := (rows 13 274 100 168 208 34 66 128 256), losses := [] }

theorem u4342 : Upper (D 7) (R 7) [12,272,96,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4343 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 7 25 112 160 66 192 448), lower := (rows 13 290 7 25 112 160 66 128 256), losses := [] }

theorem u4343 : Upper (D 7) (R 7) [12,288,3,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4344 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 7 25 112 160 192 194 322), lower := (rows 13 290 7 25 112 160 192 128 256), losses := [] }

theorem u4344 : Upper (D 7) (R 7) [12,288,3,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4345 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 144, targets := 2 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,1)], upper := (rows 13 290 7 25 208 96 66 160 416), lower := (rows 13 290 7 25 208 96 66 128 256), losses := [] }

theorem u4345 : Upper (D 7) (R 7) [12,288,3,17,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4346 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 386, targets := 64 },{ cop := 7, region := 112, targets := 2 }], pairs := [(1,0),(1,6),(4,0),(4,1)], upper := (rows 13 290 7 25 208 96 96 130 386), lower := (rows 13 290 7 25 208 96 96 128 256), losses := [] }

theorem u4346 : Upper (D 7) (R 7) [12,288,3,17,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4347 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 7 25 208 96 192 162 290), lower := (rows 13 290 7 25 208 96 192 128 256), losses := [] }

theorem u4347 : Upper (D 7) (R 7) [12,288,3,17,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4348 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 7 56 81 160 66 192 448), lower := (rows 13 290 7 56 81 160 66 128 256), losses := [] }

theorem u4348 : Upper (D 7) (R 7) [12,288,3,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4349 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(3,1),(4,5)], upper := (rows 13 290 7 56 81 160 192 194 322), lower := (rows 13 290 7 56 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 13 352 5 120 121 224 224 224 256) }] }

theorem u4349 : Upper (D 7) (R 7) [12,288,3,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 7 56 82 160 65 192 448), lower := (rows 13 290 7 56 82 160 65 128 256), losses := [] }

theorem u4350 : Upper (D 7) (R 7) [12,288,3,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4351 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(3,0),(3,1),(4,0),(4,5)], upper := (rows 13 290 7 56 82 160 192 193 321), lower := (rows 13 290 7 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 224 224 128 256), good := (rows 12 378 30 120 122 224 224 224 256) },{ target := 1, region := (rows 1 0 4 24 16 229 229 133 261), good := (rows 493 352 485 120 120 224 224 224 256) }] }

theorem u4351 : Upper (D 7) (R 7) [12,288,3,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4352 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 7 73 112 160 66 144 400), lower := (rows 13 290 7 73 112 160 66 128 256), losses := [] }

theorem u4352 : Upper (D 7) (R 7) [12,288,3,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4353 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 7 73 112 160 80 130 386), lower := (rows 13 290 7 73 112 160 80 128 256), losses := [] }

theorem u4353 : Upper (D 7) (R 7) [12,288,3,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4353 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 7 73 112 160 192 146 274), lower := (rows 13 290 7 73 112 160 192 128 256), losses := [] }

theorem u4354 : Upper (D 7) (R 7) [12,288,3,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4355 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 13 290 7 73 146 160 80 224 352), lower := (rows 13 290 7 73 146 160 80 128 256), losses := [] }

theorem u4355 : Upper (D 7) (R 7) [12,288,3,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4355 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4356 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 7 73 146 160 96 208 336), lower := (rows 13 290 7 73 146 160 96 128 256), losses := [] }

theorem u4356 : Upper (D 7) (R 7) [12,288,3,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4357 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 7 73 208 160 66 176 304), lower := (rows 13 290 7 73 208 160 66 128 256), losses := [] }

theorem u4357 : Upper (D 7) (R 7) [12,288,3,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4358 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 290 7 73 208 160 80 162 290), lower := (rows 13 290 7 73 208 160 80 128 256), losses := [] }

theorem u4358 : Upper (D 7) (R 7) [12,288,3,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4358 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4359 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 7 73 208 160 96 146 274), lower := (rows 13 290 7 73 208 160 96 128 256), losses := [] }

theorem u4359 : Upper (D 7) (R 7) [12,288,3,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4360 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 7 88 49 160 66 192 448), lower := (rows 13 290 7 88 49 160 66 128 256), losses := [] }

theorem u4360 : Upper (D 7) (R 7) [12,288,3,80,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 13 290 7 88 49 160 192 194 322), lower := (rows 13 290 7 88 49 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 13 352 5 120 121 224 224 224 256) },{ target := 5, region := (rows 1 2 4 24 16 0 231 134 262), good := (rows 461 450 455 88 89 192 192 192 256) }] }

theorem u4361 : Upper (D 7) (R 7) [12,288,3,80,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4362 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 5, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,1)], upper := (rows 13 290 7 88 145 160 66 224 352), lower := (rows 13 290 7 88 145 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 249 64 200 328), good := (rows 445 288 53 504 177 160 480 160 256) }] }

theorem u4362 : Upper (D 7) (R 7) [12,288,3,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4363 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 104, targets := 2 },{ cop := 5, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,1)], upper := (rows 13 290 7 88 145 160 96 194 322), lower := (rows 13 290 7 88 145 160 96 128 256), losses := [] }

theorem u4363 : Upper (D 7) (R 7) [12,288,3,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4364 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 77, targets := 32 },{ cop := 4, region := 77, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(3,5)], upper := (rows 13 290 7 88 146 96 65 160 416), lower := (rows 13 290 7 88 146 96 65 128 256), losses := [] }

theorem u4364 : Upper (D 7) (R 7) [12,288,3,80,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4365 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 2, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(3,7),(4,5)], upper := (rows 13 290 7 88 146 96 96 129 385), lower := (rows 13 290 7 88 146 96 96 128 256), losses := [] }

theorem u4365 : Upper (D 7) (R 7) [12,288,3,80,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4366 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 13 290 7 88 146 96 192 161 289), lower := (rows 13 290 7 88 146 96 192 128 256), losses := [] }

theorem u4366 : Upper (D 7) (R 7) [12,288,3,80,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 290 7 88 146 160 65 224 352), lower := (rows 13 290 7 88 146 160 65 128 256), losses := [] }

theorem u4367 : Upper (D 7) (R 7) [12,288,3,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4368 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(0,7),(2,7),(3,0),(3,1)], upper := (rows 13 290 7 88 146 160 96 193 321), lower := (rows 13 290 7 88 146 160 96 128 256), losses := [{ target := 7, region := (rows 25 2 20 24 16 32 98 0 284), good := (rows 269 354 327 349 351 96 96 0 256) }] }

theorem u4368 : Upper (D 7) (R 7) [12,288,3,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4369 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 290 7 88 176 33 66 192 448), lower := (rows 13 290 7 88 176 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 37 64 200 328), good := (rows 445 288 53 472 176 49 448 128 256) }] }

theorem u4369 : Upper (D 7) (R 7) [12,288,3,80,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4370 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 5, region := 450, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 290 7 88 176 33 192 194 322), lower := (rows 13 290 7 88 176 33 192 128 256), losses := [] }

theorem u4370 : Upper (D 7) (R 7) [12,288,3,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4371 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 8, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 7 88 176 34 65 192 448), lower := (rows 13 290 7 88 176 34 65 128 256), losses := [] }

theorem u4371 : Upper (D 7) (R 7) [12,288,3,80,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4372 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 13 290 7 88 176 34 192 193 321), lower := (rows 13 290 7 88 176 34 192 128 256), losses := [] }

theorem u4372 : Upper (D 7) (R 7) [12,288,3,80,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4372 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 7 88 176 96 65 130 386), lower := (rows 13 290 7 88 176 96 65 128 256), losses := [] }

theorem u4373 : Upper (D 7) (R 7) [12,288,3,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4374 : Route 9 := (fun mask => (mask,id))

def c4374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4374 : Upper (D 7) (R 7) [12,288,3,80,160,64,2] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,160,64,2] 13 (by decide) (choices 1) [1] r4374 c4374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u340

def b4375 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 13 290 7 88 176 96 192 131 259), lower := (rows 13 290 7 88 176 96 192 128 256), losses := [] }

theorem u4375 : Upper (D 7) (R 7) [12,288,3,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4376 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 7 104 82 160 65 144 400), lower := (rows 13 290 7 104 82 160 65 128 256), losses := [] }

theorem u4376 : Upper (D 7) (R 7) [12,288,3,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4377 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 7 104 82 160 80 129 385), lower := (rows 13 290 7 104 82 160 80 128 256), losses := [] }

theorem u4377 : Upper (D 7) (R 7) [12,288,3,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4377 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4378 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 7 104 82 160 192 145 273), lower := (rows 13 290 7 104 82 160 192 128 256), losses := [] }

theorem u4378 : Upper (D 7) (R 7) [12,288,3,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4379 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 7 104 145 160 66 208 336), lower := (rows 13 290 7 104 145 160 66 128 256), losses := [] }

theorem u4379 : Upper (D 7) (R 7) [12,288,3,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P07
