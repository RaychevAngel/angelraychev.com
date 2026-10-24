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

def b15360 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 152 273 34 98 162 290), lower := (rows 193 7 76 152 273 32 64 128 256), losses := [] }

theorem u15360 : Upper (D 8) (R 8) [192,5,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15361 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 152 274 33 97 161 289), lower := (rows 193 7 76 152 274 32 64 128 256), losses := [] }

theorem u15361 : Upper (D 8) (R 8) [192,5,72,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15362 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 152 304 35 99 163 291), lower := (rows 193 7 76 152 304 32 64 128 256), losses := [] }

theorem u15362 : Upper (D 8) (R 8) [192,5,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15363 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 168 49 306 370 434 306), lower := (rows 193 7 76 168 49 32 64 128 256), losses := [] }

theorem u15363 : Upper (D 8) (R 8) [192,5,72,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15364 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 168 50 305 369 433 305), lower := (rows 193 7 76 168 50 32 64 128 256), losses := [] }

theorem u15364 : Upper (D 8) (R 8) [192,5,72,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15365 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 168 273 50 114 178 306), lower := (rows 193 7 76 168 273 32 64 128 256), losses := [] }

theorem u15365 : Upper (D 8) (R 8) [192,5,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15366 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 168 274 49 113 177 305), lower := (rows 193 7 76 168 274 32 64 128 256), losses := [] }

theorem u15366 : Upper (D 8) (R 8) [192,5,72,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15367 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 168 304 51 115 179 307), lower := (rows 193 7 76 168 304 32 64 128 256), losses := [] }

theorem u15367 : Upper (D 8) (R 8) [192,5,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15368 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 265 50 176 240 176 432), lower := (rows 193 7 76 265 50 32 64 128 256), losses := [] }

theorem u15368 : Upper (D 8) (R 8) [192,5,72,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15369 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 265 146 48 112 176 304), lower := (rows 193 7 76 265 146 32 64 128 256), losses := [] }

theorem u15369 : Upper (D 8) (R 8) [192,5,72,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15370 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 265 176 50 114 178 306), lower := (rows 193 7 76 265 176 32 64 128 256), losses := [] }

theorem u15370 : Upper (D 8) (R 8) [192,5,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15371 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 266 49 176 240 176 432), lower := (rows 193 7 76 266 49 32 64 128 256), losses := [] }

theorem u15371 : Upper (D 8) (R 8) [192,5,72,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15372 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 266 176 49 113 177 305), lower := (rows 193 7 76 266 176 32 64 128 256), losses := [] }

theorem u15372 : Upper (D 8) (R 8) [192,5,72,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15373 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 280 49 162 226 162 418), lower := (rows 193 7 76 280 49 32 64 128 256), losses := [] }

theorem u15373 : Upper (D 8) (R 8) [192,5,72,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15374 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 280 50 161 225 161 417), lower := (rows 193 7 76 280 50 32 64 128 256), losses := [] }

theorem u15374 : Upper (D 8) (R 8) [192,5,72,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15375 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 280 146 33 97 161 289), lower := (rows 193 7 76 280 146 32 64 128 256), losses := [] }

theorem u15375 : Upper (D 8) (R 8) [192,5,72,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15376 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 280 176 35 99 163 291), lower := (rows 193 7 76 280 176 32 64 128 256), losses := [] }

theorem u15376 : Upper (D 8) (R 8) [192,5,72,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15377 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 296 49 178 242 178 434), lower := (rows 193 7 76 296 49 32 64 128 256), losses := [] }

theorem u15377 : Upper (D 8) (R 8) [192,5,72,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15378 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 296 50 177 241 177 433), lower := (rows 193 7 76 296 50 32 64 128 256), losses := [] }

theorem u15378 : Upper (D 8) (R 8) [192,5,72,288,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15379 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 296 146 49 113 177 305), lower := (rows 193 7 76 296 146 32 64 128 256), losses := [] }

theorem u15379 : Upper (D 8) (R 8) [192,5,72,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15380 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 296 176 51 115 179 307), lower := (rows 193 7 76 296 176 32 64 128 256), losses := [] }

theorem u15380 : Upper (D 8) (R 8) [192,5,72,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15381 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 392 49 50 114 178 306), lower := (rows 193 7 76 392 49 32 64 128 256), losses := [] }

theorem u15381 : Upper (D 8) (R 8) [192,5,72,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15382 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 392 50 49 113 177 305), lower := (rows 193 7 76 392 50 32 64 128 256), losses := [] }

theorem u15382 : Upper (D 8) (R 8) [192,5,72,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15383 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 25 274 168 232 168 424), lower := (rows 193 7 100 25 274 32 64 128 256), losses := [] }

theorem u15383 : Upper (D 8) (R 8) [192,5,96,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15384 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 25 280 162 226 162 418), lower := (rows 193 7 100 25 280 32 64 128 256), losses := [] }

theorem u15384 : Upper (D 8) (R 8) [192,5,96,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15385 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 25 304 170 234 170 426), lower := (rows 193 7 100 25 304 32 64 128 256), losses := [] }

theorem u15385 : Upper (D 8) (R 8) [192,5,96,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15386 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 49 424 488 424 424), lower := (rows 193 7 100 26 49 32 64 128 256), losses := [] }

theorem u15386 : Upper (D 8) (R 8) [192,5,96,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15387 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 56 417 481 417 417), lower := (rows 193 7 100 26 56 32 64 128 256), losses := [] }

theorem u15387 : Upper (D 8) (R 8) [192,5,96,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15387 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15388 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 176 297 361 425 297), lower := (rows 193 7 100 26 176 32 64 128 256), losses := [] }

theorem u15388 : Upper (D 8) (R 8) [192,5,96,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15389 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 273 168 232 168 424), lower := (rows 193 7 100 26 273 32 64 128 256), losses := [] }

theorem u15389 : Upper (D 8) (R 8) [192,5,96,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15390 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 280 161 225 161 417), lower := (rows 193 7 100 26 280 32 64 128 256), losses := [] }

theorem u15390 : Upper (D 8) (R 8) [192,5,96,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15391 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 304 169 233 169 425), lower := (rows 193 7 100 26 304 32 64 128 256), losses := [] }

theorem u15391 : Upper (D 8) (R 8) [192,5,96,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15392 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 400 41 105 169 297), lower := (rows 193 7 100 26 400 32 64 128 256), losses := [] }

theorem u15392 : Upper (D 8) (R 8) [192,5,96,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15393 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 50 440 472 408 408), lower := (rows 193 7 100 41 50 32 64 128 256), losses := [] }

theorem u15393 : Upper (D 8) (R 8) [192,5,96,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15394 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 146 312 376 440 312), lower := (rows 193 7 100 41 146 32 64 128 256), losses := [] }

theorem u15394 : Upper (D 8) (R 8) [192,5,96,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15395 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 152 306 370 434 306), lower := (rows 193 7 100 41 152 32 64 128 256), losses := [] }

theorem u15395 : Upper (D 8) (R 8) [192,5,96,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15396 : PairBound 9 := { available := 282, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 176 314 346 410 282), lower := (rows 193 7 100 41 176 32 64 128 256), losses := [] }

theorem u15396 : Upper (D 8) (R 8) [192,5,96,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15397 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 274 184 248 184 440), lower := (rows 193 7 100 41 274 32 64 128 256), losses := [] }

theorem u15397 : Upper (D 8) (R 8) [192,5,96,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15398 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 280 178 242 178 434), lower := (rows 193 7 100 41 280 32 64 128 256), losses := [] }

theorem u15398 : Upper (D 8) (R 8) [192,5,96,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15399 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 304 186 218 154 410), lower := (rows 193 7 100 41 304 32 64 128 256), losses := [] }

theorem u15399 : Upper (D 8) (R 8) [192,5,96,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15400 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 400 58 122 186 314), lower := (rows 193 7 100 41 400 32 64 128 256), losses := [] }

theorem u15400 : Upper (D 8) (R 8) [192,5,96,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15401 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 152 305 369 433 305), lower := (rows 193 7 100 42 152 32 64 128 256), losses := [] }

theorem u15401 : Upper (D 8) (R 8) [192,5,96,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15402 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 176 313 345 409 281), lower := (rows 193 7 100 42 176 32 64 128 256), losses := [] }

theorem u15402 : Upper (D 8) (R 8) [192,5,96,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15403 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 273 184 248 184 440), lower := (rows 193 7 100 42 273 32 64 128 256), losses := [] }

theorem u15403 : Upper (D 8) (R 8) [192,5,96,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15404 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 280 177 241 177 433), lower := (rows 193 7 100 42 280 32 64 128 256), losses := [] }

theorem u15404 : Upper (D 8) (R 8) [192,5,96,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15405 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 304 185 217 153 409), lower := (rows 193 7 100 42 304 32 64 128 256), losses := [] }

theorem u15405 : Upper (D 8) (R 8) [192,5,96,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15406 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 400 57 121 185 313), lower := (rows 193 7 100 42 400 32 64 128 256), losses := [] }

theorem u15406 : Upper (D 8) (R 8) [192,5,96,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15407 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 56 146 297 361 425 297), lower := (rows 193 7 100 56 146 32 64 128 256), losses := [] }

theorem u15407 : Upper (D 8) (R 8) [192,5,96,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15408 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 56 273 170 234 170 426), lower := (rows 193 7 100 56 273 32 64 128 256), losses := [] }

theorem u15408 : Upper (D 8) (R 8) [192,5,96,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15409 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 56 274 169 233 169 425), lower := (rows 193 7 100 56 274 32 64 128 256), losses := [] }

theorem u15409 : Upper (D 8) (R 8) [192,5,96,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15410 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 56 280 163 227 163 419), lower := (rows 193 7 100 56 280 32 64 128 256), losses := [] }

theorem u15410 : Upper (D 8) (R 8) [192,5,96,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15411 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 56 400 43 107 171 299), lower := (rows 193 7 100 56 400 32 64 128 256), losses := [] }

theorem u15411 : Upper (D 8) (R 8) [192,5,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15412 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 138 273 56 120 184 312), lower := (rows 193 7 100 138 273 32 64 128 256), losses := [] }

theorem u15412 : Upper (D 8) (R 8) [192,5,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15413 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 138 280 49 113 177 305), lower := (rows 193 7 100 138 280 32 64 128 256), losses := [] }

theorem u15413 : Upper (D 8) (R 8) [192,5,96,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15414 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 138 304 57 121 185 313), lower := (rows 193 7 100 138 304 32 64 128 256), losses := [] }

theorem u15414 : Upper (D 8) (R 8) [192,5,96,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15415 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 152 273 42 106 170 298), lower := (rows 193 7 100 152 273 32 64 128 256), losses := [] }

theorem u15415 : Upper (D 8) (R 8) [192,5,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15416 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 152 274 41 105 169 297), lower := (rows 193 7 100 152 274 32 64 128 256), losses := [] }

theorem u15416 : Upper (D 8) (R 8) [192,5,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15417 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 152 304 43 107 171 299), lower := (rows 193 7 100 152 304 32 64 128 256), losses := [] }

theorem u15417 : Upper (D 8) (R 8) [192,5,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15418 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 168 273 58 122 186 314), lower := (rows 193 7 100 168 273 32 64 128 256), losses := [] }

theorem u15418 : Upper (D 8) (R 8) [192,5,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15419 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 168 274 57 121 185 313), lower := (rows 193 7 100 168 274 32 64 128 256), losses := [] }

theorem u15419 : Upper (D 8) (R 8) [192,5,96,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15419
end Delivery.IrregularNine14.P08
