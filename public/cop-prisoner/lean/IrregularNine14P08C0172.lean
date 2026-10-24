import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0048

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10320 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 140 304 240 240 240 496), lower := (rows 67 35 13 140 304 32 64 128 256), losses := [] }

theorem u10320 : Upper (D 8) (R 8) [66,33,9,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10321 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 140 336 176 240 176 432), lower := (rows 67 35 13 140 336 32 64 128 256), losses := [] }

theorem u10321 : Upper (D 8) (R 8) [66,33,9,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10322 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 140 400 112 112 240 368), lower := (rows 67 35 13 140 400 32 64 128 256), losses := [] }

theorem u10322 : Upper (D 8) (R 8) [66,33,9,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10323 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 152 52 480 480 480 480), lower := (rows 67 35 13 152 52 32 64 128 256), losses := [] }

theorem u10323 : Upper (D 8) (R 8) [66,33,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10324 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 152 84 416 480 416 416), lower := (rows 67 35 13 152 84 32 64 128 256), losses := [] }

theorem u10324 : Upper (D 8) (R 8) [66,33,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10325 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 152 276 224 224 224 480), lower := (rows 67 35 13 152 276 32 64 128 256), losses := [] }

theorem u10325 : Upper (D 8) (R 8) [66,33,9,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10326 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 152 304 228 228 228 484), lower := (rows 67 35 13 152 304 32 64 128 256), losses := [] }

theorem u10326 : Upper (D 8) (R 8) [66,33,9,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10327 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 152 336 164 228 164 420), lower := (rows 67 35 13 152 336 32 64 128 256), losses := [] }

theorem u10327 : Upper (D 8) (R 8) [66,33,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10328 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 52 496 464 464 464), lower := (rows 67 35 13 168 52 32 64 128 256), losses := [] }

theorem u10328 : Upper (D 8) (R 8) [66,33,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10329 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 84 432 496 432 432), lower := (rows 67 35 13 168 84 32 64 128 256), losses := [] }

theorem u10329 : Upper (D 8) (R 8) [66,33,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10330 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 148 368 368 496 368), lower := (rows 67 35 13 168 148 32 64 128 256), losses := [] }

theorem u10330 : Upper (D 8) (R 8) [66,33,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10331 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 208 308 372 436 308), lower := (rows 67 35 13 168 208 32 64 128 256), losses := [] }

theorem u10331 : Upper (D 8) (R 8) [66,33,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10332 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 276 240 240 240 496), lower := (rows 67 35 13 168 276 32 64 128 256), losses := [] }

theorem u10332 : Upper (D 8) (R 8) [66,33,9,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10333 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 304 244 212 212 468), lower := (rows 67 35 13 168 304 32 64 128 256), losses := [] }

theorem u10333 : Upper (D 8) (R 8) [66,33,9,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10334 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 336 180 244 180 436), lower := (rows 67 35 13 168 336 32 64 128 256), losses := [] }

theorem u10334 : Upper (D 8) (R 8) [66,33,9,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10335 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 168 400 116 116 244 372), lower := (rows 67 35 13 168 400 32 64 128 256), losses := [] }

theorem u10335 : Upper (D 8) (R 8) [66,33,9,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10336 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 52 432 496 432 432), lower := (rows 67 35 13 200 52 32 64 128 256), losses := [] }

theorem u10336 : Upper (D 8) (R 8) [66,33,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10337 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 148 304 368 432 304), lower := (rows 67 35 13 200 148 32 64 128 256), losses := [] }

theorem u10337 : Upper (D 8) (R 8) [66,33,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10338 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 176 308 372 436 308), lower := (rows 67 35 13 200 176 32 64 128 256), losses := [] }

theorem u10338 : Upper (D 8) (R 8) [66,33,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10339 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 276 176 240 176 432), lower := (rows 67 35 13 200 276 32 64 128 256), losses := [] }

theorem u10339 : Upper (D 8) (R 8) [66,33,9,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10340 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 304 180 244 180 436), lower := (rows 67 35 13 200 304 32 64 128 256), losses := [] }

theorem u10340 : Upper (D 8) (R 8) [66,33,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10341 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 200 400 52 116 180 308), lower := (rows 67 35 13 200 400 32 64 128 256), losses := [] }

theorem u10341 : Upper (D 8) (R 8) [66,33,9,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10342 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 268 176 240 240 240 496), lower := (rows 67 35 13 268 176 32 64 128 256), losses := [] }

theorem u10342 : Upper (D 8) (R 8) [66,33,9,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10343 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 268 208 176 240 176 432), lower := (rows 67 35 13 268 208 32 64 128 256), losses := [] }

theorem u10343 : Upper (D 8) (R 8) [66,33,9,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10344 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 280 52 224 224 224 480), lower := (rows 67 35 13 280 52 32 64 128 256), losses := [] }

theorem u10344 : Upper (D 8) (R 8) [66,33,9,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10345 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 280 84 160 224 160 416), lower := (rows 67 35 13 280 84 32 64 128 256), losses := [] }

theorem u10345 : Upper (D 8) (R 8) [66,33,9,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10346 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 280 148 224 224 224 480), lower := (rows 67 35 13 280 148 32 64 128 256), losses := [] }

theorem u10346 : Upper (D 8) (R 8) [66,33,9,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10347 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 280 176 228 228 228 484), lower := (rows 67 35 13 280 176 32 64 128 256), losses := [] }

theorem u10347 : Upper (D 8) (R 8) [66,33,9,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10348 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 280 208 164 228 164 420), lower := (rows 67 35 13 280 208 32 64 128 256), losses := [] }

theorem u10348 : Upper (D 8) (R 8) [66,33,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10349 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 296 52 240 208 208 464), lower := (rows 67 35 13 296 52 32 64 128 256), losses := [] }

theorem u10349 : Upper (D 8) (R 8) [66,33,9,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10350 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 296 84 176 240 176 432), lower := (rows 67 35 13 296 84 32 64 128 256), losses := [] }

theorem u10350 : Upper (D 8) (R 8) [66,33,9,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10351 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 296 148 240 240 240 496), lower := (rows 67 35 13 296 148 32 64 128 256), losses := [] }

theorem u10351 : Upper (D 8) (R 8) [66,33,9,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10352 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 296 176 244 212 212 468), lower := (rows 67 35 13 296 176 32 64 128 256), losses := [] }

theorem u10352 : Upper (D 8) (R 8) [66,33,9,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10353 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 296 208 180 244 180 436), lower := (rows 67 35 13 296 208 32 64 128 256), losses := [] }

theorem u10353 : Upper (D 8) (R 8) [66,33,9,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10354 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 328 52 176 240 176 432), lower := (rows 67 35 13 328 52 32 64 128 256), losses := [] }

theorem u10354 : Upper (D 8) (R 8) [66,33,9,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10355 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 328 148 176 240 176 432), lower := (rows 67 35 13 328 148 32 64 128 256), losses := [] }

theorem u10355 : Upper (D 8) (R 8) [66,33,9,320,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10356 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 328 176 180 244 180 436), lower := (rows 67 35 13 328 176 32 64 128 256), losses := [] }

theorem u10356 : Upper (D 8) (R 8) [66,33,9,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10357 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 392 52 240 240 240 496), lower := (rows 67 35 13 392 52 32 64 128 256), losses := [] }

theorem u10357 : Upper (D 8) (R 8) [66,33,9,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10358 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 392 84 176 240 176 432), lower := (rows 67 35 13 392 84 32 64 128 256), losses := [] }

theorem u10358 : Upper (D 8) (R 8) [66,33,9,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10359 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 392 148 112 112 240 368), lower := (rows 67 35 13 392 148 32 64 128 256), losses := [] }

theorem u10359 : Upper (D 8) (R 8) [66,33,9,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10360 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 392 176 116 116 244 372), lower := (rows 67 35 13 392 176 32 64 128 256), losses := [] }

theorem u10360 : Upper (D 8) (R 8) [66,33,9,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10361 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 67 35 13 392 208 52 116 180 308), lower := (rows 67 35 13 392 208 32 64 128 256), losses := [] }

theorem u10361 : Upper (D 8) (R 8) [66,33,9,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10362 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 67 35 28 41 52 480 448 448 448), lower := (rows 67 35 28 41 52 32 64 128 256), losses := [] }

theorem u10362 : Upper (D 8) (R 8) [66,33,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10363 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 148 480 480 480 480), lower := (rows 67 35 28 41 148 32 64 128 256), losses := [] }

theorem u10363 : Upper (D 8) (R 8) [66,33,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10364 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 176 484 452 452 452), lower := (rows 67 35 28 41 176 32 64 128 256), losses := [] }

theorem u10364 : Upper (D 8) (R 8) [66,33,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10365 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 208 420 484 420 420), lower := (rows 67 35 28 41 208 32 64 128 256), losses := [] }

theorem u10365 : Upper (D 8) (R 8) [66,33,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10366 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 276 224 224 224 480), lower := (rows 67 35 28 41 276 32 64 128 256), losses := [] }

theorem u10366 : Upper (D 8) (R 8) [66,33,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10367 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 304 228 196 196 452), lower := (rows 67 35 28 41 304 32 64 128 256), losses := [] }

theorem u10367 : Upper (D 8) (R 8) [66,33,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10368 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 336 164 228 164 420), lower := (rows 67 35 28 41 336 32 64 128 256), losses := [] }

theorem u10368 : Upper (D 8) (R 8) [66,33,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10369 : PairBound 9 := { available := 228, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 67 35 28 41 400 228 228 228 484), lower := (rows 67 35 28 41 400 32 64 128 256), losses := [] }

theorem u10369 : Upper (D 8) (R 8) [66,33,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10370 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 44 81 416 480 416 416), lower := (rows 67 35 28 44 81 32 64 128 256), losses := [] }

theorem u10370 : Upper (D 8) (R 8) [66,33,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10371 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 112 417 449 385 385), lower := (rows 67 35 28 44 112 32 64 128 256), losses := [] }

theorem u10371 : Upper (D 8) (R 8) [66,33,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10372 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 145 480 480 480 480), lower := (rows 67 35 28 44 145 32 64 128 256), losses := [] }

theorem u10372 : Upper (D 8) (R 8) [66,33,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10373 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 176 481 449 449 449), lower := (rows 67 35 28 44 176 32 64 128 256), losses := [] }

theorem u10373 : Upper (D 8) (R 8) [66,33,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10374 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 44 208 417 481 417 417), lower := (rows 67 35 28 44 208 32 64 128 256), losses := [] }

theorem u10374 : Upper (D 8) (R 8) [66,33,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10375 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 273 224 224 224 480), lower := (rows 67 35 28 44 273 32 64 128 256), losses := [] }

theorem u10375 : Upper (D 8) (R 8) [66,33,24,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10376 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 35 28 44 304 225 193 193 449), lower := (rows 67 35 28 44 304 32 64 128 256), losses := [] }

theorem u10376 : Upper (D 8) (R 8) [66,33,24,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10377 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 44 336 161 225 161 417), lower := (rows 67 35 28 44 336 32 64 128 256), losses := [] }

theorem u10377 : Upper (D 8) (R 8) [66,33,24,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10378 : Route 9 := (fun mask => (mask,id))

def c10378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10378 : Upper (D 8) (R 8) [66,33,24,36,384] 13 := by
  apply FastRouting.sound _ _ [66,33,24,36,384] 13 (by decide) (choices 1) [1,64,128] r10378 c10378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2882
  · exact u2883
  · exact u2884

def b10379 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 35 28 73 148 416 480 416 416), lower := (rows 67 35 28 73 148 32 64 128 256), losses := [] }

theorem u10379 : Upper (D 8) (R 8) [66,33,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u10379
end Delivery.IrregularNine14.P08
