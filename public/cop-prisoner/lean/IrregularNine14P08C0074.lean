import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0010

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 97 7 164 137 304 34 88 216 344), lower := (rows 97 7 164 137 304 34 64 128 256), losses := [] }

theorem u4440 : Upper (D 8) (R 8) [96,5,160,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4440 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4441 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 97 7 164 137 304 40 82 210 338), lower := (rows 97 7 164 137 304 40 64 128 256), losses := [] }

theorem u4441 : Upper (D 8) (R 8) [96,5,160,129,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4441 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4442 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 97 7 164 137 304 48 74 202 330), lower := (rows 97 7 164 137 304 48 64 128 256), losses := [] }

theorem u4442 : Upper (D 8) (R 8) [96,5,160,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4442 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4443 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 137 304 96 90 154 282), lower := (rows 97 7 164 137 304 96 64 128 256), losses := [] }

theorem u4443 : Upper (D 8) (R 8) [96,5,160,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4444 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 7 164 137 336 34 120 184 312), lower := (rows 97 7 164 137 336 34 64 128 256), losses := [] }

theorem u4444 : Upper (D 8) (R 8) [96,5,160,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4444 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 7 164 137 336 40 114 178 306), lower := (rows 97 7 164 137 336 40 64 128 256), losses := [] }

theorem u4445 : Upper (D 8) (R 8) [96,5,160,129,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4445 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4446 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 7 164 137 336 48 106 170 298), lower := (rows 97 7 164 137 336 48 64 128 256), losses := [] }

theorem u4446 : Upper (D 8) (R 8) [96,5,160,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4446 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4447 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 97 7 164 152 273 34 104 232 360), lower := (rows 97 7 164 152 273 34 64 128 256), losses := [] }

theorem u4447 : Upper (D 8) (R 8) [96,5,160,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4447 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4448 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 164 152 273 40 98 226 354), lower := (rows 97 7 164 152 273 40 64 128 256), losses := [] }

theorem u4448 : Upper (D 8) (R 8) [96,5,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4448 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 152 273 96 106 170 298), lower := (rows 97 7 164 152 273 96 64 128 256), losses := [] }

theorem u4449 : Upper (D 8) (R 8) [96,5,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 74, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 152 304 33 74 202 330), lower := (rows 97 7 164 152 304 33 64 128 256), losses := [] }

theorem u4450 : Upper (D 8) (R 8) [96,5,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4451 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 164 152 304 34 73 201 329), lower := (rows 97 7 164 152 304 34 64 128 256), losses := [] }

theorem u4451 : Upper (D 8) (R 8) [96,5,160,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4451 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4452 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 164 152 304 40 67 195 323), lower := (rows 97 7 164 152 304 40 64 128 256), losses := [] }

theorem u4452 : Upper (D 8) (R 8) [96,5,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4452 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4453 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 164 152 304 96 75 139 267), lower := (rows 97 7 164 152 304 96 64 128 256), losses := [] }

theorem u4453 : Upper (D 8) (R 8) [96,5,160,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4454 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 152 336 33 106 170 298), lower := (rows 97 7 164 152 336 33 64 128 256), losses := [] }

theorem u4454 : Upper (D 8) (R 8) [96,5,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 164 152 336 34 105 169 297), lower := (rows 97 7 164 152 336 34 64 128 256), losses := [] }

theorem u4455 : Upper (D 8) (R 8) [96,5,160,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4455 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4456 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 164 152 336 40 99 163 291), lower := (rows 97 7 164 152 336 40 64 128 256), losses := [] }

theorem u4456 : Upper (D 8) (R 8) [96,5,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4456 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4457 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 97 7 164 200 273 34 120 184 312), lower := (rows 97 7 164 200 273 34 64 128 256), losses := [] }

theorem u4457 : Upper (D 8) (R 8) [96,5,160,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4457 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4458 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 97 7 164 200 273 40 114 178 306), lower := (rows 97 7 164 200 273 40 64 128 256), losses := [] }

theorem u4458 : Upper (D 8) (R 8) [96,5,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4458 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 97 7 164 200 273 48 106 170 298), lower := (rows 97 7 164 200 273 48 64 128 256), losses := [] }

theorem u4459 : Upper (D 8) (R 8) [96,5,160,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4459 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4460 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 200 274 33 120 184 312), lower := (rows 97 7 164 200 274 33 64 128 256), losses := [] }

theorem u4460 : Upper (D 8) (R 8) [96,5,160,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4461 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 164 200 274 40 113 177 305), lower := (rows 97 7 164 200 274 40 64 128 256), losses := [] }

theorem u4461 : Upper (D 8) (R 8) [96,5,160,192,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4461 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4462 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 164 200 274 48 105 169 297), lower := (rows 97 7 164 200 274 48 64 128 256), losses := [] }

theorem u4462 : Upper (D 8) (R 8) [96,5,160,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4462 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4463 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 200 280 33 114 178 306), lower := (rows 97 7 164 200 280 33 64 128 256), losses := [] }

theorem u4463 : Upper (D 8) (R 8) [96,5,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4464 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 164 200 280 34 113 177 305), lower := (rows 97 7 164 200 280 34 64 128 256), losses := [] }

theorem u4464 : Upper (D 8) (R 8) [96,5,160,192,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4464 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4465 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 97 7 164 200 280 48 99 163 291), lower := (rows 97 7 164 200 280 48 64 128 256), losses := [] }

theorem u4465 : Upper (D 8) (R 8) [96,5,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4465 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 164 200 304 33 90 154 282), lower := (rows 97 7 164 200 304 33 64 128 256), losses := [] }

theorem u4466 : Upper (D 8) (R 8) [96,5,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 7 164 200 304 34 89 153 281), lower := (rows 97 7 164 200 304 34 64 128 256), losses := [] }

theorem u4467 : Upper (D 8) (R 8) [96,5,160,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4467 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 7 164 200 304 40 83 147 275), lower := (rows 97 7 164 200 304 40 64 128 256), losses := [] }

theorem u4468 : Upper (D 8) (R 8) [96,5,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4468 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 7 164 200 304 48 75 139 267), lower := (rows 97 7 164 200 304 48 64 128 256), losses := [] }

theorem u4469 : Upper (D 8) (R 8) [96,5,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4469 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 152, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 152 33 224 224 480), lower := (rows 97 7 262 56 152 33 64 128 256), losses := [] }

theorem u4470 : Upper (D 8) (R 8) [96,5,258,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4471 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 56 152 96 225 161 417), lower := (rows 97 7 262 56 152 96 64 128 256), losses := [] }

theorem u4471 : Upper (D 8) (R 8) [96,5,258,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4472 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 152 160 97 225 353), lower := (rows 97 7 262 56 152 160 64 128 256), losses := [] }

theorem u4472 : Upper (D 8) (R 8) [96,5,258,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 152, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 208 33 232 168 424), lower := (rows 97 7 262 56 208 33 64 128 256), losses := [] }

theorem u4473 : Upper (D 8) (R 8) [96,5,258,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 262 56 208 40 225 161 417), lower := (rows 97 7 262 56 208 40 64 128 256), losses := [] }

theorem u4474 : Upper (D 8) (R 8) [96,5,258,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4474 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4475 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 56 208 160 105 169 297), lower := (rows 97 7 262 56 208 160 64 128 256), losses := [] }

theorem u4475 : Upper (D 8) (R 8) [96,5,258,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4476 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 152, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 88 176 33 232 168 424), lower := (rows 97 7 262 88 176 33 64 128 256), losses := [] }

theorem u4476 : Upper (D 8) (R 8) [96,5,258,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4477 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 262 88 176 40 225 161 417), lower := (rows 97 7 262 88 176 40 64 128 256), losses := [] }

theorem u4477 : Upper (D 8) (R 8) [96,5,258,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4477 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 73, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 88 176 160 105 169 297), lower := (rows 97 7 262 88 176 160 64 128 256), losses := [] }

theorem u4478 : Upper (D 8) (R 8) [96,5,258,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4479 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 152, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 168 208 33 120 184 312), lower := (rows 97 7 262 168 208 33 64 128 256), losses := [] }

theorem u4479 : Upper (D 8) (R 8) [96,5,258,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4480 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 97 7 262 168 208 40 113 177 305), lower := (rows 97 7 262 168 208 40 64 128 256), losses := [] }

theorem u4480 : Upper (D 8) (R 8) [96,5,258,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4480 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4481 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 97 7 262 168 208 48 105 169 297), lower := (rows 97 7 262 168 208 48 64 128 256), losses := [] }

theorem u4481 : Upper (D 8) (R 8) [96,5,258,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4481 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4482 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 268 26 176 33 224 224 480), lower := (rows 97 7 268 26 176 33 64 128 256), losses := [] }

theorem u4482 : Upper (D 8) (R 8) [96,5,264,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4483 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 26 176 96 225 161 417), lower := (rows 97 7 268 26 176 96 64 128 256), losses := [] }

theorem u4483 : Upper (D 8) (R 8) [96,5,264,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4484 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 26 176 160 97 225 353), lower := (rows 97 7 268 26 176 160 64 128 256), losses := [] }

theorem u4484 : Upper (D 8) (R 8) [96,5,264,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4485 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 268 42 145 48 224 224 480), lower := (rows 97 7 268 42 145 48 64 128 256), losses := [] }

theorem u4485 : Upper (D 8) (R 8) [96,5,264,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4485 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4486 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 42 145 96 240 176 432), lower := (rows 97 7 268 42 145 96 64 128 256), losses := [] }

theorem u4486 : Upper (D 8) (R 8) [96,5,264,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4487 : Route 9 := (fun mask => (mask,id))

def c4487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4487 : Upper (D 8) (R 8) [96,5,264,34,129,128] 13 := by
  apply FastRouting.sound _ _ [96,5,264,34,129,128] 13 (by decide) (choices 1) [16,32] r4487 c4487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u604
  · exact u605

def b4488 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 42 176 33 208 208 464), lower := (rows 97 7 268 42 176 33 64 128 256), losses := [] }

theorem u4488 : Upper (D 8) (R 8) [96,5,264,34,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4489 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 268 42 176 48 193 193 449), lower := (rows 97 7 268 42 176 48 64 128 256), losses := [] }

theorem u4489 : Upper (D 8) (R 8) [96,5,264,34,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4489 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4490 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 42 176 96 209 145 401), lower := (rows 97 7 268 42 176 96 64 128 256), losses := [] }

theorem u4490 : Upper (D 8) (R 8) [96,5,264,34,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4491 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 42 176 160 81 209 337), lower := (rows 97 7 268 42 176 160 64 128 256), losses := [] }

theorem u4491 : Upper (D 8) (R 8) [96,5,264,34,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4492 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 268 42 208 33 240 176 432), lower := (rows 97 7 268 42 208 33 64 128 256), losses := [] }

theorem u4492 : Upper (D 8) (R 8) [96,5,264,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4493 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 97 7 268 42 208 48 225 161 417), lower := (rows 97 7 268 42 208 48 64 128 256), losses := [] }

theorem u4493 : Upper (D 8) (R 8) [96,5,264,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4493 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r4494 : Route 9 := (fun mask => (mask,id))

def c4494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4494 : Upper (D 8) (R 8) [96,5,264,34,192,128] 13 := by
  apply FastRouting.sound _ _ [96,5,264,34,192,128] 13 (by decide) (choices 1) [1,16,32] r4494 c4494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u606
  · exact u607
  · exact u608

def b4495 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 268 56 145 34 224 224 480), lower := (rows 97 7 268 56 145 34 64 128 256), losses := [] }

theorem u4495 : Upper (D 8) (R 8) [96,5,264,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4495 [(5,1)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4496 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 56 145 96 226 162 418), lower := (rows 97 7 268 56 145 96 64 128 256), losses := [] }

theorem u4496 : Upper (D 8) (R 8) [96,5,264,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4497 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 56 145 160 98 226 354), lower := (rows 97 7 268 56 145 160 64 128 256), losses := [] }

theorem u4497 : Upper (D 8) (R 8) [96,5,264,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4498 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 268 56 146 33 224 224 480), lower := (rows 97 7 268 56 146 33 64 128 256), losses := [] }

theorem u4498 : Upper (D 8) (R 8) [96,5,264,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4499 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 56 146 96 225 161 417), lower := (rows 97 7 268 56 146 96 64 128 256), losses := [] }

theorem u4499 : Upper (D 8) (R 8) [96,5,264,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4499
end Delivery.IrregularNine14.P08
