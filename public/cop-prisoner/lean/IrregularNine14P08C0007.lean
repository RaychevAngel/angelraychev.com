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

def b420 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 261 104 152 160 96 145 273), lower := (rows 67 38 261 104 152 160 96 128 256), losses := [] }

theorem u420 : Upper (D 8) (R 8) [66,36,257,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 268 25 176 96 65 160 416), lower := (rows 67 38 268 25 176 96 65 128 256), losses := [] }

theorem u421 : Upper (D 8) (R 8) [66,36,264,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 25 176 96 96 129 385), lower := (rows 67 38 268 25 176 96 96 128 256), losses := [] }

theorem u422 : Upper (D 8) (R 8) [66,36,264,17,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 268 25 176 96 192 161 289), lower := (rows 67 38 268 25 176 96 192 128 256), losses := [] }

theorem u423 : Upper (D 8) (R 8) [66,36,264,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 41 112 160 65 144 400), lower := (rows 67 38 268 41 112 160 65 128 256), losses := [] }

theorem u424 : Upper (D 8) (R 8) [66,36,264,33,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 38 268 41 112 160 80 129 385), lower := (rows 67 38 268 41 112 160 80 128 256), losses := [] }

theorem u425 : Upper (D 8) (R 8) [66,36,264,33,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b425 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 41 112 160 192 145 273), lower := (rows 67 38 268 41 112 160 192 128 256), losses := [] }

theorem u426 : Upper (D 8) (R 8) [66,36,264,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 41 208 160 65 176 304), lower := (rows 67 38 268 41 208 160 65 128 256), losses := [] }

theorem u427 : Upper (D 8) (R 8) [66,36,264,33,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 268 41 208 160 80 161 289), lower := (rows 67 38 268 41 208 160 80 128 256), losses := [] }

theorem u428 : Upper (D 8) (R 8) [66,36,264,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b428 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 41 208 160 96 145 273), lower := (rows 67 38 268 41 208 160 96 128 256), losses := [] }

theorem u429 : Upper (D 8) (R 8) [66,36,264,33,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 168 208 33 65 176 304), lower := (rows 67 38 268 168 208 33 65 128 256), losses := [] }

theorem u430 : Upper (D 8) (R 8) [66,36,264,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 268 168 208 33 80 161 289), lower := (rows 67 38 268 168 208 33 80 128 256), losses := [] }

theorem u431 : Upper (D 8) (R 8) [66,36,264,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b431 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 268 168 208 33 96 145 273), lower := (rows 67 38 268 168 208 33 96 128 256), losses := [] }

theorem u432 : Upper (D 8) (R 8) [66,36,264,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 67 38 388 25 176 33 72 224 352), lower := (rows 67 38 388 25 176 33 72 128 256), losses := [] }

theorem u433 : Upper (D 8) (R 8) [66,36,384,17,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b433 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 25 176 33 96 200 328), lower := (rows 67 38 388 25 176 33 96 128 256), losses := [] }

theorem u434 : Upper (D 8) (R 8) [66,36,384,17,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 25 176 96 65 168 296), lower := (rows 67 38 388 25 176 96 65 128 256), losses := [] }

theorem u435 : Upper (D 8) (R 8) [66,36,384,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 388 25 176 96 72 161 289), lower := (rows 67 38 388 25 176 96 72 128 256), losses := [] }

theorem u436 : Upper (D 8) (R 8) [66,36,384,17,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b436 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 25 176 96 96 137 265), lower := (rows 67 38 388 25 176 96 96 128 256), losses := [] }

theorem u437 : Upper (D 8) (R 8) [66,36,384,17,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 390, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 388 56 208 33 65 168 296), lower := (rows 67 38 388 56 208 33 65 128 256), losses := [] }

theorem u438 : Upper (D 8) (R 8) [66,36,384,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 388 56 208 33 72 161 289), lower := (rows 67 38 388 56 208 33 72 128 256), losses := [] }

theorem u439 : Upper (D 8) (R 8) [66,36,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b439 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 56 208 33 96 137 265), lower := (rows 67 38 388 56 208 33 96 128 256), losses := [] }

theorem u440 : Upper (D 8) (R 8) [66,36,384,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 88 176 33 65 168 296), lower := (rows 67 38 388 88 176 33 65 128 256), losses := [] }

theorem u441 : Upper (D 8) (R 8) [66,36,384,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 388 88 176 33 72 161 289), lower := (rows 67 38 388 88 176 33 72 128 256), losses := [] }

theorem u442 : Upper (D 8) (R 8) [66,36,384,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b442 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 388 88 176 33 96 137 265), lower := (rows 67 38 388 88 176 33 96 128 256), losses := [] }

theorem u443 : Upper (D 8) (R 8) [66,36,384,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 88 304 160 65 164 292), lower := (rows 67 131 44 88 304 160 65 128 256), losses := [] }

theorem u444 : Upper (D 8) (R 8) [66,129,40,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 44 88 304 160 68 161 289), lower := (rows 67 131 44 88 304 160 68 128 256), losses := [] }

theorem u445 : Upper (D 8) (R 8) [66,129,40,80,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b445 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 88 304 160 96 133 261), lower := (rows 67 131 44 88 304 160 96 128 256), losses := [] }

theorem u446 : Upper (D 8) (R 8) [66,129,40,80,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 412, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 152 304 96 65 164 292), lower := (rows 67 131 44 152 304 96 65 128 256), losses := [] }

theorem u447 : Upper (D 8) (R 8) [66,129,40,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 131 44 152 304 96 68 161 289), lower := (rows 67 131 44 152 304 96 68 128 256), losses := [] }

theorem u448 : Upper (D 8) (R 8) [66,129,40,144,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b448 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 67 131 44 152 304 96 96 133 261), lower := (rows 67 131 44 152 304 96 96 128 256), losses := [] }

theorem u449 : Upper (D 8) (R 8) [66,129,40,144,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 296 176 96 65 176 304), lower := (rows 67 134 13 296 176 96 65 128 256), losses := [] }

theorem u450 : Upper (D 8) (R 8) [66,132,9,288,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 13 296 176 96 80 161 289), lower := (rows 67 134 13 296 176 96 80 128 256), losses := [] }

theorem u451 : Upper (D 8) (R 8) [66,132,9,288,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b451 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 13 296 176 96 96 145 273), lower := (rows 67 134 13 296 176 96 96 128 256), losses := [] }

theorem u452 : Upper (D 8) (R 8) [66,132,9,288,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 134 44 25 304 160 65 224 352), lower := (rows 67 134 44 25 304 160 65 128 256), losses := [] }

theorem u453 : Upper (D 8) (R 8) [66,132,40,17,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 65, camps := [], pairs := [(0,7)], upper := (rows 67 134 44 25 304 160 96 193 321), lower := (rows 67 134 44 25 304 160 96 128 256), losses := [{ target := 7, region := (rows 3 2 4 10 20 32 116 0 267), good := (rows 331 351 380 345 368 96 96 0 256) }] }

theorem u454 : Upper (D 8) (R 8) [66,132,40,17,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 390, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 292 56 208 33 65 168 296), lower := (rows 67 134 292 56 208 33 65 128 256), losses := [] }

theorem u455 : Upper (D 8) (R 8) [66,132,288,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 292 56 208 33 72 161 289), lower := (rows 67 134 292 56 208 33 72 128 256), losses := [] }

theorem u456 : Upper (D 8) (R 8) [66,132,288,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b456 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 292 56 208 33 96 137 265), lower := (rows 67 134 292 56 208 33 96 128 256), losses := [] }

theorem u457 : Upper (D 8) (R 8) [66,132,288,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 134 292 88 176 33 65 168 296), lower := (rows 67 134 292 88 176 33 65 128 256), losses := [] }

theorem u458 : Upper (D 8) (R 8) [66,132,288,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 292 88 176 33 72 161 289), lower := (rows 67 134 292 88 176 33 72 128 256), losses := [] }

theorem u459 : Upper (D 8) (R 8) [66,132,288,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b459 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 292 88 176 33 96 137 265), lower := (rows 67 134 292 88 176 33 96 128 256), losses := [] }

theorem u460 : Upper (D 8) (R 8) [66,132,288,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 28 304 96 65 160 416), lower := (rows 67 162 13 28 304 96 65 128 256), losses := [] }

theorem u461 : Upper (D 8) (R 8) [66,160,9,20,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 28 304 96 96 129 385), lower := (rows 67 162 13 28 304 96 96 128 256), losses := [] }

theorem u462 : Upper (D 8) (R 8) [66,160,9,20,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 316, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 28 304 96 192 161 289), lower := (rows 67 162 13 28 304 96 192 128 256), losses := [] }

theorem u463 : Upper (D 8) (R 8) [66,160,9,20,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 130, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 56 276 96 65 160 416), lower := (rows 67 162 13 56 276 96 65 128 256), losses := [] }

theorem u464 : Upper (D 8) (R 8) [66,160,9,48,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 67 162 13 56 276 96 96 129 385), lower := (rows 67 162 13 56 276 96 96 128 256), losses := [] }

theorem u465 : Upper (D 8) (R 8) [66,160,9,48,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 316, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 56 276 96 192 161 289), lower := (rows 67 162 13 56 276 96 192 128 256), losses := [] }

theorem u466 : Upper (D 8) (R 8) [66,160,9,48,260,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 67 162 13 56 400 33 68 224 352), lower := (rows 67 162 13 56 400 33 68 128 256), losses := [] }

theorem u467 : Upper (D 8) (R 8) [66,160,9,48,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b467 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 56 400 33 96 196 324), lower := (rows 67 162 13 56 400 33 96 128 256), losses := [] }

theorem u468 : Upper (D 8) (R 8) [66,160,9,48,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 13 56 400 96 65 164 292), lower := (rows 67 162 13 56 400 96 65 128 256), losses := [] }

theorem u469 : Upper (D 8) (R 8) [66,160,9,48,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 13 56 400 96 68 161 289), lower := (rows 67 162 13 56 400 96 68 128 256), losses := [] }

theorem u470 : Upper (D 8) (R 8) [66,160,9,48,384,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b470 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 67 162 13 56 400 96 96 133 261), lower := (rows 67 162 13 56 400 96 96 128 256), losses := [] }

theorem u471 : Upper (D 8) (R 8) [66,160,9,48,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 13 296 148 96 65 176 304), lower := (rows 67 162 13 296 148 96 65 128 256), losses := [] }

theorem u472 : Upper (D 8) (R 8) [66,160,9,288,132,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 13 296 148 96 80 161 289), lower := (rows 67 162 13 296 148 96 80 128 256), losses := [] }

theorem u473 : Upper (D 8) (R 8) [66,160,9,288,132,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b473 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 67 162 13 296 148 96 96 145 273), lower := (rows 67 162 13 296 148 96 96 128 256), losses := [] }

theorem u474 : Upper (D 8) (R 8) [66,160,9,288,132,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 67 162 13 296 208 33 68 176 304), lower := (rows 67 162 13 296 208 33 68 128 256), losses := [] }

theorem u475 : Upper (D 8) (R 8) [66,160,9,288,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b475 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 67 162 13 296 208 33 80 164 292), lower := (rows 67 162 13 296 208 33 80 128 256), losses := [] }

theorem u476 : Upper (D 8) (R 8) [66,160,9,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b476 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 296 208 33 96 148 276), lower := (rows 67 162 13 296 208 33 96 128 256), losses := [] }

theorem u477 : Upper (D 8) (R 8) [66,160,9,288,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 162 28 200 304 33 65 164 292), lower := (rows 67 162 28 200 304 33 65 128 256), losses := [] }

theorem u478 : Upper (D 8) (R 8) [66,160,24,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 28 200 304 33 68 161 289), lower := (rows 67 162 28 200 304 33 68 128 256), losses := [] }

theorem u479 : Upper (D 8) (R 8) [66,160,24,192,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b479 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P08
