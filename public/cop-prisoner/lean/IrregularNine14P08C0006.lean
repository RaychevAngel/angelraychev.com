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

def b360 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 392, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 21 296 176 96 65 160 416), lower := (rows 67 14 21 296 176 96 65 128 256), losses := [] }

theorem u360 : Upper (D 8) (R 8) [66,12,17,288,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 21 296 176 96 96 129 385), lower := (rows 67 14 21 296 176 96 96 128 256), losses := [] }

theorem u361 : Upper (D 8) (R 8) [66,12,17,288,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 128 }], pairs := [(3,7)], upper := (rows 67 14 21 296 176 96 192 161 289), lower := (rows 67 14 21 296 176 96 192 128 256), losses := [] }

theorem u362 : Upper (D 8) (R 8) [66,12,17,288,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 296 112 160 65 144 400), lower := (rows 67 14 37 296 112 160 65 128 256), losses := [] }

theorem u363 : Upper (D 8) (R 8) [66,12,33,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 14 37 296 112 160 80 129 385), lower := (rows 67 14 37 296 112 160 80 128 256), losses := [] }

theorem u364 : Upper (D 8) (R 8) [66,12,33,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b364 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 296 112 160 192 145 273), lower := (rows 67 14 37 296 112 160 192 128 256), losses := [] }

theorem u365 : Upper (D 8) (R 8) [66,12,33,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 296 208 160 65 176 304), lower := (rows 67 14 37 296 208 160 65 128 256), losses := [] }

theorem u366 : Upper (D 8) (R 8) [66,12,33,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 37 296 208 160 80 161 289), lower := (rows 67 14 37 296 208 160 80 128 256), losses := [] }

theorem u367 : Upper (D 8) (R 8) [66,12,33,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b367 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 37 296 208 160 96 145 273), lower := (rows 67 14 37 296 208 160 96 128 256), losses := [] }

theorem u368 : Upper (D 8) (R 8) [66,12,33,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 133 296 112 160 65 176 304), lower := (rows 67 14 133 296 112 160 65 128 256), losses := [] }

theorem u369 : Upper (D 8) (R 8) [66,12,129,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 133 296 112 160 80 161 289), lower := (rows 67 14 133 296 112 160 80 128 256), losses := [] }

theorem u370 : Upper (D 8) (R 8) [66,12,129,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b370 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 67 14 133 296 112 160 96 145 273), lower := (rows 67 14 133 296 112 160 96 128 256), losses := [] }

theorem u371 : Upper (D 8) (R 8) [66,12,129,288,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 65, targets := 32 }], pairs := [(0,5)], upper := (rows 67 14 164 296 208 33 65 176 304), lower := (rows 67 14 164 296 208 33 65 128 256), losses := [] }

theorem u372 : Upper (D 8) (R 8) [66,12,160,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 14 164 296 208 33 80 161 289), lower := (rows 67 14 164 296 208 33 80 128 256), losses := [] }

theorem u373 : Upper (D 8) (R 8) [66,12,160,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b373 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 67 14 164 296 208 33 96 145 273), lower := (rows 67 14 164 296 208 33 96 128 256), losses := [] }

theorem u374 : Upper (D 8) (R 8) [66,12,160,288,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 308, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 200 304 160 65 164 292), lower := (rows 67 35 28 200 304 160 65 128 256), losses := [] }

theorem u375 : Upper (D 8) (R 8) [66,33,24,192,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 35 28 200 304 160 68 161 289), lower := (rows 67 35 28 200 304 160 68 128 256), losses := [] }

theorem u376 : Upper (D 8) (R 8) [66,33,24,192,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b376 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 28 200 304 160 96 133 261), lower := (rows 67 35 28 200 304 160 96 128 256), losses := [] }

theorem u377 : Upper (D 8) (R 8) [66,33,24,192,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 88 304 160 65 132 388), lower := (rows 67 35 44 88 304 160 65 128 256), losses := [] }

theorem u378 : Upper (D 8) (R 8) [66,33,40,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 35 44 88 304 160 68 129 385), lower := (rows 67 35 44 88 304 160 68 128 256), losses := [] }

theorem u379 : Upper (D 8) (R 8) [66,33,40,80,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b379 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0)], upper := (rows 67 35 44 88 304 160 192 133 261), lower := (rows 67 35 44 88 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 224 224 128 256), good := (rows 98 98 108 124 380 224 224 224 256) }] }

theorem u380 : Upper (D 8) (R 8) [66,33,40,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 268 208 160 65 176 304), lower := (rows 67 35 44 268 208 160 65 128 256), losses := [] }

theorem u381 : Upper (D 8) (R 8) [66,33,40,260,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 35 44 268 208 160 80 161 289), lower := (rows 67 35 44 268 208 160 80 128 256), losses := [] }

theorem u382 : Upper (D 8) (R 8) [66,33,40,260,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b382 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 268 208 160 96 145 273), lower := (rows 67 35 44 268 208 160 96 128 256), losses := [] }

theorem u383 : Upper (D 8) (R 8) [66,33,40,260,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 44 328 148 160 65 176 304), lower := (rows 67 35 44 328 148 160 65 128 256), losses := [] }

theorem u384 : Upper (D 8) (R 8) [66,33,40,320,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 35 44 328 148 160 80 161 289), lower := (rows 67 35 44 328 148 160 80 128 256), losses := [] }

theorem u385 : Upper (D 8) (R 8) [66,33,40,320,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b385 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 44 328 148 160 96 145 273), lower := (rows 67 35 44 328 148 160 96 128 256), losses := [] }

theorem u386 : Upper (D 8) (R 8) [66,33,40,320,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 76 152 304 160 65 164 292), lower := (rows 67 35 76 152 304 160 65 128 256), losses := [] }

theorem u387 : Upper (D 8) (R 8) [66,33,72,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 35 76 152 304 160 68 161 289), lower := (rows 67 35 76 152 304 160 68 128 256), losses := [] }

theorem u388 : Upper (D 8) (R 8) [66,33,72,144,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b388 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 152 304 160 96 133 261), lower := (rows 67 35 76 152 304 160 96 128 256), losses := [] }

theorem u389 : Upper (D 8) (R 8) [66,33,72,144,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 76 296 148 160 65 176 304), lower := (rows 67 35 76 296 148 160 65 128 256), losses := [] }

theorem u390 : Upper (D 8) (R 8) [66,33,72,288,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 35 76 296 148 160 80 161 289), lower := (rows 67 35 76 296 148 160 80 128 256), losses := [] }

theorem u391 : Upper (D 8) (R 8) [66,33,72,288,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b391 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 67 35 76 296 148 160 96 145 273), lower := (rows 67 35 76 296 148 160 96 128 256), losses := [] }

theorem u392 : Upper (D 8) (R 8) [66,33,72,288,132,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 296 112 160 65 144 400), lower := (rows 67 38 13 296 112 160 65 128 256), losses := [] }

theorem u393 : Upper (D 8) (R 8) [66,36,9,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 38 13 296 112 160 80 129 385), lower := (rows 67 38 13 296 112 160 80 128 256), losses := [] }

theorem u394 : Upper (D 8) (R 8) [66,36,9,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b394 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 296 112 160 192 145 273), lower := (rows 67 38 13 296 112 160 192 128 256), losses := [] }

theorem u395 : Upper (D 8) (R 8) [66,36,9,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 296 208 160 65 176 304), lower := (rows 67 38 13 296 208 160 65 128 256), losses := [] }

theorem u396 : Upper (D 8) (R 8) [66,36,9,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 13 296 208 160 80 161 289), lower := (rows 67 38 13 296 208 160 80 128 256), losses := [] }

theorem u397 : Upper (D 8) (R 8) [66,36,9,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b397 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 13 296 208 160 96 145 273), lower := (rows 67 38 13 296 208 160 96 128 256), losses := [] }

theorem u398 : Upper (D 8) (R 8) [66,36,9,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 28 137 304 96 65 160 416), lower := (rows 67 38 28 137 304 96 65 128 256), losses := [] }

theorem u399 : Upper (D 8) (R 8) [66,36,24,129,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 67 38 28 137 304 96 96 129 385), lower := (rows 67 38 28 137 304 96 96 128 256), losses := [] }

theorem u400 : Upper (D 8) (R 8) [66,36,24,129,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 28 137 304 96 192 161 289), lower := (rows 67 38 28 137 304 96 192 128 256), losses := [] }

theorem u401 : Upper (D 8) (R 8) [66,36,24,129,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 28 168 273 96 65 160 416), lower := (rows 67 38 28 168 273 96 65 128 256), losses := [] }

theorem u402 : Upper (D 8) (R 8) [66,36,24,160,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 67 38 28 168 273 96 96 129 385), lower := (rows 67 38 28 168 273 96 96 128 256), losses := [] }

theorem u403 : Upper (D 8) (R 8) [66,36,24,160,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 128 }], pairs := [(4,7)], upper := (rows 67 38 28 168 273 96 192 161 289), lower := (rows 67 38 28 168 273 96 192 128 256), losses := [] }

theorem u404 : Upper (D 8) (R 8) [66,36,24,160,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 140 25 304 96 65 160 416), lower := (rows 67 38 140 25 304 96 65 128 256), losses := [] }

theorem u405 : Upper (D 8) (R 8) [66,36,136,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 25 304 96 96 129 385), lower := (rows 67 38 140 25 304 96 96 128 256), losses := [] }

theorem u406 : Upper (D 8) (R 8) [66,36,136,17,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 312, targets := 128 }], pairs := [(3,7)], upper := (rows 67 38 140 25 304 96 192 161 289), lower := (rows 67 38 140 25 304 96 192 128 256), losses := [] }

theorem u407 : Upper (D 8) (R 8) [66,36,136,17,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 67 38 140 265 176 96 65 176 304), lower := (rows 67 38 140 265 176 96 65 128 256), losses := [] }

theorem u408 : Upper (D 8) (R 8) [66,36,136,257,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 140 265 176 96 80 161 289), lower := (rows 67 38 140 265 176 96 80 128 256), losses := [] }

theorem u409 : Upper (D 8) (R 8) [66,36,136,257,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b409 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 67 38 140 265 176 96 96 145 273), lower := (rows 67 38 140 265 176 96 96 128 256), losses := [] }

theorem u410 : Upper (D 8) (R 8) [66,36,136,257,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 296 176 33 65 208 336), lower := (rows 67 38 140 296 176 33 65 128 256), losses := [] }

theorem u411 : Upper (D 8) (R 8) [66,36,136,288,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 67 38 140 296 176 33 80 193 321), lower := (rows 67 38 140 296 176 33 80 128 256), losses := [] }

theorem u412 : Upper (D 8) (R 8) [66,36,136,288,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b412 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 296 176 96 65 145 273), lower := (rows 67 38 140 296 176 96 65 128 256), losses := [] }

theorem u413 : Upper (D 8) (R 8) [66,36,136,288,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 67 38 140 296 176 96 80 129 257), lower := (rows 67 38 140 296 176 96 80 128 256), losses := [] }

theorem u414 : Upper (D 8) (R 8) [66,36,136,288,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b414 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 296 208 33 65 176 304), lower := (rows 67 38 140 296 208 33 65 128 256), losses := [] }

theorem u415 : Upper (D 8) (R 8) [66,36,136,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 140 296 208 33 80 161 289), lower := (rows 67 38 140 296 208 33 80 128 256), losses := [] }

theorem u416 : Upper (D 8) (R 8) [66,36,136,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b416 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 67 38 140 296 208 33 96 145 273), lower := (rows 67 38 140 296 208 33 96 128 256), losses := [] }

theorem u417 : Upper (D 8) (R 8) [66,36,136,288,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 67 38 261 104 152 160 65 176 304), lower := (rows 67 38 261 104 152 160 65 128 256), losses := [] }

theorem u418 : Upper (D 8) (R 8) [66,36,257,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 38 261 104 152 160 80 161 289), lower := (rows 67 38 261 104 152 160 80 128 256), losses := [] }

theorem u419 : Upper (D 8) (R 8) [66,36,257,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b419 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P08
