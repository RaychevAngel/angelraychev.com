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

def b4380 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 97 7 164 56 208 40 323 387 259), lower := (rows 97 7 164 56 208 40 64 128 256), losses := [] }

theorem u4380 : Upper (D 8) (R 8) [96,5,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4380 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4381 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 7 164 56 208 288 75 139 267), lower := (rows 97 7 164 56 208 288 64 128 256), losses := [] }

theorem u4381 : Upper (D 8) (R 8) [96,5,160,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4381 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4382 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 97 7 164 56 273 34 200 200 456), lower := (rows 97 7 164 56 273 34 64 128 256), losses := [] }

theorem u4382 : Upper (D 8) (R 8) [96,5,160,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4382 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4383 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 97 7 164 56 273 40 194 194 450), lower := (rows 97 7 164 56 273 40 64 128 256), losses := [] }

theorem u4383 : Upper (D 8) (R 8) [96,5,160,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4383 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4384 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 56 273 96 202 138 394), lower := (rows 97 7 164 56 273 96 64 128 256), losses := [] }

theorem u4384 : Upper (D 8) (R 8) [96,5,160,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4385 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 273 160 74 202 330), lower := (rows 97 7 164 56 273 160 64 128 256), losses := [] }

theorem u4385 : Upper (D 8) (R 8) [96,5,160,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4386 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 164 56 274 33 200 200 456), lower := (rows 97 7 164 56 274 33 64 128 256), losses := [] }

theorem u4386 : Upper (D 8) (R 8) [96,5,160,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4387 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 164 56 274 40 193 193 449), lower := (rows 97 7 164 56 274 40 64 128 256), losses := [] }

theorem u4387 : Upper (D 8) (R 8) [96,5,160,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4387 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4388 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 56 274 96 201 137 393), lower := (rows 97 7 164 56 274 96 64 128 256), losses := [] }

theorem u4388 : Upper (D 8) (R 8) [96,5,160,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4389 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 274 160 73 201 329), lower := (rows 97 7 164 56 274 160 64 128 256), losses := [] }

theorem u4389 : Upper (D 8) (R 8) [96,5,160,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4390 : PairBound 9 := { available := 194, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 280 33 194 194 450), lower := (rows 97 7 164 56 280 33 64 128 256), losses := [] }

theorem u4390 : Upper (D 8) (R 8) [96,5,160,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4391 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 164 56 280 34 193 193 449), lower := (rows 97 7 164 56 280 34 64 128 256), losses := [] }

theorem u4391 : Upper (D 8) (R 8) [96,5,160,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4391 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4392 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 56 280 96 195 131 387), lower := (rows 97 7 164 56 280 96 64 128 256), losses := [] }

theorem u4392 : Upper (D 8) (R 8) [96,5,160,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4393 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 280 160 67 195 323), lower := (rows 97 7 164 56 280 160 64 128 256), losses := [] }

theorem u4393 : Upper (D 8) (R 8) [96,5,160,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4394 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 336 33 202 138 394), lower := (rows 97 7 164 56 336 33 64 128 256), losses := [] }

theorem u4394 : Upper (D 8) (R 8) [96,5,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4395 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 164 56 336 34 201 137 393), lower := (rows 97 7 164 56 336 34 64 128 256), losses := [] }

theorem u4395 : Upper (D 8) (R 8) [96,5,160,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4395 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4396 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 7 164 56 336 40 195 131 387), lower := (rows 97 7 164 56 336 40 64 128 256), losses := [] }

theorem u4396 : Upper (D 8) (R 8) [96,5,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4396 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4397 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 336 160 75 139 267), lower := (rows 97 7 164 56 336 160 64 128 256), losses := [] }

theorem u4397 : Upper (D 8) (R 8) [96,5,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4398 : PairBound 9 := { available := 74, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 56 400 33 74 202 330), lower := (rows 97 7 164 56 400 33 64 128 256), losses := [] }

theorem u4398 : Upper (D 8) (R 8) [96,5,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4399 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 164 56 400 34 73 201 329), lower := (rows 97 7 164 56 400 34 64 128 256), losses := [] }

theorem u4399 : Upper (D 8) (R 8) [96,5,160,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4399 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4400 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 164 56 400 40 67 195 323), lower := (rows 97 7 164 56 400 40 64 128 256), losses := [] }

theorem u4400 : Upper (D 8) (R 8) [96,5,160,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4400 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4401 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 56 400 96 75 139 267), lower := (rows 97 7 164 56 400 96 64 128 256), losses := [] }

theorem u4401 : Upper (D 8) (R 8) [96,5,160,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4402 : PairBound 9 := { available := 304, camps := [], pairs := [], upper := (rows 97 7 164 74 145 40 368 432 304), lower := (rows 97 7 164 74 145 40 64 128 256), losses := [] }

theorem u4402 : Upper (D 8) (R 8) [96,5,160,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4402 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4403 : PairBound 9 := { available := 296, camps := [], pairs := [], upper := (rows 97 7 164 74 145 48 360 424 296), lower := (rows 97 7 164 74 145 48 64 128 256), losses := [] }

theorem u4403 : Upper (D 8) (R 8) [96,5,160,66,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4403 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4404 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 7 164 74 145 288 120 184 312), lower := (rows 97 7 164 74 145 288 64 128 256), losses := [] }

theorem u4404 : Upper (D 8) (R 8) [96,5,160,66,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4404 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4405 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 97 7 164 74 273 40 240 176 432), lower := (rows 97 7 164 74 273 40 64 128 256), losses := [] }

theorem u4405 : Upper (D 8) (R 8) [96,5,160,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4405 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4406 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 7 164 74 273 48 232 168 424), lower := (rows 97 7 164 74 273 48 64 128 256), losses := [] }

theorem u4406 : Upper (D 8) (R 8) [96,5,160,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4406 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4407 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 273 160 120 184 312), lower := (rows 97 7 164 74 273 160 64 128 256), losses := [] }

theorem u4407 : Upper (D 8) (R 8) [96,5,160,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4408 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 280 33 240 176 432), lower := (rows 97 7 164 74 280 33 64 128 256), losses := [] }

theorem u4408 : Upper (D 8) (R 8) [96,5,160,66,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4409 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 164 74 280 48 225 161 417), lower := (rows 97 7 164 74 280 48 64 128 256), losses := [] }

theorem u4409 : Upper (D 8) (R 8) [96,5,160,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4409 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4410 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 280 160 113 177 305), lower := (rows 97 7 164 74 280 160 64 128 256), losses := [] }

theorem u4410 : Upper (D 8) (R 8) [96,5,160,66,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4411 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 304 33 216 152 408), lower := (rows 97 7 164 74 304 33 64 128 256), losses := [] }

theorem u4411 : Upper (D 8) (R 8) [96,5,160,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4412 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 97 7 164 74 304 40 209 145 401), lower := (rows 97 7 164 74 304 40 64 128 256), losses := [] }

theorem u4412 : Upper (D 8) (R 8) [96,5,160,66,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4412 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 164 74 304 48 201 137 393), lower := (rows 97 7 164 74 304 48 64 128 256), losses := [] }

theorem u4413 : Upper (D 8) (R 8) [96,5,160,66,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4413 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4414 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 304 160 89 153 281), lower := (rows 97 7 164 74 304 160 64 128 256), losses := [] }

theorem u4414 : Upper (D 8) (R 8) [96,5,160,66,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4415 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 74 400 33 120 184 312), lower := (rows 97 7 164 74 400 33 64 128 256), losses := [] }

theorem u4415 : Upper (D 8) (R 8) [96,5,160,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4416 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 164 74 400 40 113 177 305), lower := (rows 97 7 164 74 400 40 64 128 256), losses := [] }

theorem u4416 : Upper (D 8) (R 8) [96,5,160,66,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4416 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4417 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 164 74 400 48 105 169 297), lower := (rows 97 7 164 74 400 48 64 128 256), losses := [] }

theorem u4417 : Upper (D 8) (R 8) [96,5,160,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4417 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 296, camps := [], pairs := [], upper := (rows 97 7 164 88 145 34 360 424 296), lower := (rows 97 7 164 88 145 34 64 128 256), losses := [] }

theorem u4418 : Upper (D 8) (R 8) [96,5,160,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4418 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4419 : PairBound 9 := { available := 290, camps := [], pairs := [], upper := (rows 97 7 164 88 145 40 354 418 290), lower := (rows 97 7 164 88 145 40 64 128 256), losses := [] }

theorem u4419 : Upper (D 8) (R 8) [96,5,160,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4419 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4420 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 7 164 88 145 288 106 170 298), lower := (rows 97 7 164 88 145 288 64 128 256), losses := [] }

theorem u4420 : Upper (D 8) (R 8) [96,5,160,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4420 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 97 7 164 88 273 34 232 168 424), lower := (rows 97 7 164 88 273 34 64 128 256), losses := [] }

theorem u4421 : Upper (D 8) (R 8) [96,5,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4421 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4422 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 97 7 164 88 273 40 226 162 418), lower := (rows 97 7 164 88 273 40 64 128 256), losses := [] }

theorem u4422 : Upper (D 8) (R 8) [96,5,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4422 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4423 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 273 160 106 170 298), lower := (rows 97 7 164 88 273 160 64 128 256), losses := [] }

theorem u4423 : Upper (D 8) (R 8) [96,5,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4424 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 274 33 232 168 424), lower := (rows 97 7 164 88 274 33 64 128 256), losses := [] }

theorem u4424 : Upper (D 8) (R 8) [96,5,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4425 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 164 88 274 40 225 161 417), lower := (rows 97 7 164 88 274 40 64 128 256), losses := [] }

theorem u4425 : Upper (D 8) (R 8) [96,5,160,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4425 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4426 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 274 160 105 169 297), lower := (rows 97 7 164 88 274 160 64 128 256), losses := [] }

theorem u4426 : Upper (D 8) (R 8) [96,5,160,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4427 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 304 33 202 138 394), lower := (rows 97 7 164 88 304 33 64 128 256), losses := [] }

theorem u4427 : Upper (D 8) (R 8) [96,5,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4428 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 97 7 164 88 304 34 201 137 393), lower := (rows 97 7 164 88 304 34 64 128 256), losses := [] }

theorem u4428 : Upper (D 8) (R 8) [96,5,160,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4428 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4429 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 97 7 164 88 304 40 195 131 387), lower := (rows 97 7 164 88 304 40 64 128 256), losses := [] }

theorem u4429 : Upper (D 8) (R 8) [96,5,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4429 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4430 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 304 160 75 139 267), lower := (rows 97 7 164 88 304 160 64 128 256), losses := [] }

theorem u4430 : Upper (D 8) (R 8) [96,5,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4431 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 88 400 33 106 170 298), lower := (rows 97 7 164 88 400 33 64 128 256), losses := [] }

theorem u4431 : Upper (D 8) (R 8) [96,5,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4432 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 164 88 400 34 105 169 297), lower := (rows 97 7 164 88 400 34 64 128 256), losses := [] }

theorem u4432 : Upper (D 8) (R 8) [96,5,160,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4432 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 164 88 400 40 99 163 291), lower := (rows 97 7 164 88 400 40 64 128 256), losses := [] }

theorem u4433 : Upper (D 8) (R 8) [96,5,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4433 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 164 137 274 40 112 240 368), lower := (rows 97 7 164 137 274 40 64 128 256), losses := [] }

theorem u4434 : Upper (D 8) (R 8) [96,5,160,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4434 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4435 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 7 164 137 274 48 104 232 360), lower := (rows 97 7 164 137 274 48 64 128 256), losses := [] }

theorem u4435 : Upper (D 8) (R 8) [96,5,160,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4435 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4436 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 137 274 96 120 184 312), lower := (rows 97 7 164 137 274 96 64 128 256), losses := [] }

theorem u4436 : Upper (D 8) (R 8) [96,5,160,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4437 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 164 137 280 34 112 240 368), lower := (rows 97 7 164 137 280 34 64 128 256), losses := [] }

theorem u4437 : Upper (D 8) (R 8) [96,5,160,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4437 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 164 137 280 48 98 226 354), lower := (rows 97 7 164 137 280 48 64 128 256), losses := [] }

theorem u4438 : Upper (D 8) (R 8) [96,5,160,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4438 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4439 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 137 280 96 114 178 306), lower := (rows 97 7 164 137 280 96 64 128 256), losses := [] }

theorem u4439 : Upper (D 8) (R 8) [96,5,160,129,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4439
end Delivery.IrregularNine14.P08
