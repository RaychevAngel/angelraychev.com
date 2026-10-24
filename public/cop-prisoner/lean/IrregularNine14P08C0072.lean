import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4320 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 140 296 208 48 99 163 291), lower := (rows 97 7 140 296 208 48 64 128 256), losses := [] }

theorem u4320 : Upper (D 8) (R 8) [96,5,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4320 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4321 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 97 7 164 25 304 34 200 200 456), lower := (rows 97 7 164 25 304 34 64 128 256), losses := [] }

theorem u4321 : Upper (D 8) (R 8) [96,5,160,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4321 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4322 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 97 7 164 25 304 40 194 194 450), lower := (rows 97 7 164 25 304 40 64 128 256), losses := [] }

theorem u4322 : Upper (D 8) (R 8) [96,5,160,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4322 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4323 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 25 304 96 202 138 394), lower := (rows 97 7 164 25 304 96 64 128 256), losses := [] }

theorem u4323 : Upper (D 8) (R 8) [96,5,160,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 25 304 160 74 202 330), lower := (rows 97 7 164 25 304 160 64 128 256), losses := [] }

theorem u4324 : Upper (D 8) (R 8) [96,5,160,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 7 164 25 400 34 104 232 360), lower := (rows 97 7 164 25 400 34 64 128 256), losses := [] }

theorem u4325 : Upper (D 8) (R 8) [96,5,160,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4325 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4326 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 164 25 400 40 98 226 354), lower := (rows 97 7 164 25 400 40 64 128 256), losses := [] }

theorem u4326 : Upper (D 8) (R 8) [96,5,160,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4326 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4327 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 25 400 96 106 170 298), lower := (rows 97 7 164 25 400 96 64 128 256), losses := [] }

theorem u4327 : Upper (D 8) (R 8) [96,5,160,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4328 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 26 56 33 448 448 448), lower := (rows 97 7 164 26 56 33 64 128 256), losses := [] }

theorem u4328 : Upper (D 8) (R 8) [96,5,160,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 26 56 96 449 385 385), lower := (rows 97 7 164 26 56 96 64 128 256), losses := [] }

theorem u4329 : Upper (D 8) (R 8) [96,5,160,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4330 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 56 160 321 449 321), lower := (rows 97 7 164 26 56 160 64 128 256), losses := [] }

theorem u4330 : Upper (D 8) (R 8) [96,5,160,18,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4331 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 164 26 56 288 193 193 449), lower := (rows 97 7 164 26 56 288 64 128 256), losses := [] }

theorem u4331 : Upper (D 8) (R 8) [96,5,160,18,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4331 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 164 26 280 33 224 224 480), lower := (rows 97 7 164 26 280 33 64 128 256), losses := [] }

theorem u4332 : Upper (D 8) (R 8) [96,5,160,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 26 280 96 225 161 417), lower := (rows 97 7 164 26 280 96 64 128 256), losses := [] }

theorem u4333 : Upper (D 8) (R 8) [96,5,160,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4334 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 280 160 97 225 353), lower := (rows 97 7 164 26 280 160 64 128 256), losses := [] }

theorem u4334 : Upper (D 8) (R 8) [96,5,160,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4335 : PairBound 9 := { available := 200, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 304 33 200 200 456), lower := (rows 97 7 164 26 304 33 64 128 256), losses := [] }

theorem u4335 : Upper (D 8) (R 8) [96,5,160,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4336 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 164 26 304 40 193 193 449), lower := (rows 97 7 164 26 304 40 64 128 256), losses := [] }

theorem u4336 : Upper (D 8) (R 8) [96,5,160,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4336 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4337 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 26 304 96 201 137 393), lower := (rows 97 7 164 26 304 96 64 128 256), losses := [] }

theorem u4337 : Upper (D 8) (R 8) [96,5,160,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4338 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 304 160 73 201 329), lower := (rows 97 7 164 26 304 160 64 128 256), losses := [] }

theorem u4338 : Upper (D 8) (R 8) [96,5,160,18,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4339 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 336 33 232 168 424), lower := (rows 97 7 164 26 336 33 64 128 256), losses := [] }

theorem u4339 : Upper (D 8) (R 8) [96,5,160,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4340 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 164 26 336 40 225 161 417), lower := (rows 97 7 164 26 336 40 64 128 256), losses := [] }

theorem u4340 : Upper (D 8) (R 8) [96,5,160,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4340 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4341 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 26 336 160 105 169 297), lower := (rows 97 7 164 26 336 160 64 128 256), losses := [] }

theorem u4341 : Upper (D 8) (R 8) [96,5,160,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4342 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 42 88 33 464 400 400), lower := (rows 97 7 164 42 88 33 64 128 256), losses := [] }

theorem u4342 : Upper (D 8) (R 8) [96,5,160,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4343 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 97 7 164 42 88 48 449 385 385), lower := (rows 97 7 164 42 88 48 64 128 256), losses := [] }

theorem u4343 : Upper (D 8) (R 8) [96,5,160,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4343 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4344 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 42 88 160 337 401 273), lower := (rows 97 7 164 42 88 160 64 128 256), losses := [] }

theorem u4344 : Upper (D 8) (R 8) [96,5,160,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4345 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 7 164 42 88 288 209 145 401), lower := (rows 97 7 164 42 88 288 64 128 256), losses := [] }

theorem u4345 : Upper (D 8) (R 8) [96,5,160,34,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4345 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4346 : PairBound 9 := { available := 336, camps := [], pairs := [], upper := (rows 97 7 164 42 145 40 336 464 336), lower := (rows 97 7 164 42 145 40 64 128 256), losses := [] }

theorem u4346 : Upper (D 8) (R 8) [96,5,160,34,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4346 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4347 : PairBound 9 := { available := 328, camps := [], pairs := [], upper := (rows 97 7 164 42 145 48 328 456 328), lower := (rows 97 7 164 42 145 48 64 128 256), losses := [] }

theorem u4347 : Upper (D 8) (R 8) [96,5,160,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4347 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4348 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 42 145 96 344 408 280), lower := (rows 97 7 164 42 145 96 64 128 256), losses := [] }

theorem u4348 : Upper (D 8) (R 8) [96,5,160,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4349 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 97 7 164 42 145 288 88 216 344), lower := (rows 97 7 164 42 145 288 64 128 256), losses := [] }

theorem u4349 : Upper (D 8) (R 8) [96,5,160,34,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4349 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 42 208 33 344 408 280), lower := (rows 97 7 164 42 208 33 64 128 256), losses := [] }

theorem u4350 : Upper (D 8) (R 8) [96,5,160,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4351 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 97 7 164 42 208 40 337 401 273), lower := (rows 97 7 164 42 208 40 64 128 256), losses := [] }

theorem u4351 : Upper (D 8) (R 8) [96,5,160,34,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4351 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4352 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 97 7 164 42 208 48 329 393 265), lower := (rows 97 7 164 42 208 48 64 128 256), losses := [] }

theorem u4352 : Upper (D 8) (R 8) [96,5,160,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4352 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4353 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 7 164 42 208 288 89 153 281), lower := (rows 97 7 164 42 208 288 64 128 256), losses := [] }

theorem u4353 : Upper (D 8) (R 8) [96,5,160,34,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4353 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 97 7 164 42 273 40 208 208 464), lower := (rows 97 7 164 42 273 40 64 128 256), losses := [] }

theorem u4354 : Upper (D 8) (R 8) [96,5,160,34,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4354 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4355 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 97 7 164 42 273 48 200 200 456), lower := (rows 97 7 164 42 273 48 64 128 256), losses := [] }

theorem u4355 : Upper (D 8) (R 8) [96,5,160,34,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4355 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4356 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 42 273 96 216 152 408), lower := (rows 97 7 164 42 273 96 64 128 256), losses := [] }

theorem u4356 : Upper (D 8) (R 8) [96,5,160,34,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4357 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 42 273 160 88 216 344), lower := (rows 97 7 164 42 273 160 64 128 256), losses := [] }

theorem u4357 : Upper (D 8) (R 8) [96,5,160,34,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4358 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 42 280 33 208 208 464), lower := (rows 97 7 164 42 280 33 64 128 256), losses := [] }

theorem u4358 : Upper (D 8) (R 8) [96,5,160,34,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4359 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 164 42 280 48 193 193 449), lower := (rows 97 7 164 42 280 48 64 128 256), losses := [] }

theorem u4359 : Upper (D 8) (R 8) [96,5,160,34,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4359 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4360 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 42 280 96 209 145 401), lower := (rows 97 7 164 42 280 96 64 128 256), losses := [] }

theorem u4360 : Upper (D 8) (R 8) [96,5,160,34,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 42 280 160 81 209 337), lower := (rows 97 7 164 42 280 160 64 128 256), losses := [] }

theorem u4361 : Upper (D 8) (R 8) [96,5,160,34,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4362 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 42 336 33 216 152 408), lower := (rows 97 7 164 42 336 33 64 128 256), losses := [] }

theorem u4362 : Upper (D 8) (R 8) [96,5,160,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4363 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 7 164 42 336 40 209 145 401), lower := (rows 97 7 164 42 336 40 64 128 256), losses := [] }

theorem u4363 : Upper (D 8) (R 8) [96,5,160,34,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4363 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4364 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 164 42 336 48 201 137 393), lower := (rows 97 7 164 42 336 48 64 128 256), losses := [] }

theorem u4364 : Upper (D 8) (R 8) [96,5,160,34,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4364 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4365 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 42 336 160 89 153 281), lower := (rows 97 7 164 42 336 160 64 128 256), losses := [] }

theorem u4365 : Upper (D 8) (R 8) [96,5,160,34,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4366 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 164 42 400 33 88 216 344), lower := (rows 97 7 164 42 400 33 64 128 256), losses := [] }

theorem u4366 : Upper (D 8) (R 8) [96,5,160,34,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 164 42 400 40 81 209 337), lower := (rows 97 7 164 42 400 40 64 128 256), losses := [] }

theorem u4367 : Upper (D 8) (R 8) [96,5,160,34,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4367 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4368 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 164 42 400 48 73 201 329), lower := (rows 97 7 164 42 400 48 64 128 256), losses := [] }

theorem u4368 : Upper (D 8) (R 8) [96,5,160,34,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4368 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4369 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 42 400 96 89 153 281), lower := (rows 97 7 164 42 400 96 64 128 256), losses := [] }

theorem u4369 : Upper (D 8) (R 8) [96,5,160,34,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4370 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 82 33 456 392 392), lower := (rows 97 7 164 56 82 33 64 128 256), losses := [] }

theorem u4370 : Upper (D 8) (R 8) [96,5,160,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4371 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 97 7 164 56 82 40 449 385 385), lower := (rows 97 7 164 56 82 40 64 128 256), losses := [] }

theorem u4371 : Upper (D 8) (R 8) [96,5,160,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4371 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4372 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 82 160 329 393 265), lower := (rows 97 7 164 56 82 160 64 128 256), losses := [] }

theorem u4372 : Upper (D 8) (R 8) [96,5,160,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 164 56 82 288 201 137 393), lower := (rows 97 7 164 56 82 288 64 128 256), losses := [] }

theorem u4373 : Upper (D 8) (R 8) [96,5,160,48,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4373 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4374 : PairBound 9 := { available := 328, camps := [], pairs := [], upper := (rows 97 7 164 56 145 34 328 456 328), lower := (rows 97 7 164 56 145 34 64 128 256), losses := [] }

theorem u4374 : Upper (D 8) (R 8) [96,5,160,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4374 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4375 : PairBound 9 := { available := 322, camps := [], pairs := [], upper := (rows 97 7 164 56 145 40 322 450 322), lower := (rows 97 7 164 56 145 40 64 128 256), losses := [] }

theorem u4375 : Upper (D 8) (R 8) [96,5,160,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4375 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4376 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 56 145 96 330 394 266), lower := (rows 97 7 164 56 145 96 64 128 256), losses := [] }

theorem u4376 : Upper (D 8) (R 8) [96,5,160,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4377 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 97 7 164 56 145 288 74 202 330), lower := (rows 97 7 164 56 145 288 64 128 256), losses := [] }

theorem u4377 : Upper (D 8) (R 8) [96,5,160,48,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4377 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4378 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 208 33 330 394 266), lower := (rows 97 7 164 56 208 33 64 128 256), losses := [] }

theorem u4378 : Upper (D 8) (R 8) [96,5,160,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4379 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 97 7 164 56 208 34 329 393 265), lower := (rows 97 7 164 56 208 34 64 128 256), losses := [] }

theorem u4379 : Upper (D 8) (R 8) [96,5,160,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4379 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P08
