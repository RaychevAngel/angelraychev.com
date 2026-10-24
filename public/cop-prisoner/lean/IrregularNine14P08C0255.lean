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

def b15300 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 26 304 168 232 168 424), lower := (rows 193 7 69 26 304 32 64 128 256), losses := [] }

theorem u15300 : Upper (D 8) (R 8) [192,5,65,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15301 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 26 400 40 104 168 296), lower := (rows 193 7 69 26 400 32 64 128 256), losses := [] }

theorem u15301 : Upper (D 8) (R 8) [192,5,65,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15302 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 42 152 304 368 432 304), lower := (rows 193 7 69 42 152 32 64 128 256), losses := [] }

theorem u15302 : Upper (D 8) (R 8) [192,5,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15303 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 42 176 312 376 440 312), lower := (rows 193 7 69 42 176 32 64 128 256), losses := [] }

theorem u15303 : Upper (D 8) (R 8) [192,5,65,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15304 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 42 280 176 240 176 432), lower := (rows 193 7 69 42 280 32 64 128 256), losses := [] }

theorem u15304 : Upper (D 8) (R 8) [192,5,65,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15305 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 42 304 184 248 184 440), lower := (rows 193 7 69 42 304 32 64 128 256), losses := [] }

theorem u15305 : Upper (D 8) (R 8) [192,5,65,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15306 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 42 400 56 120 184 312), lower := (rows 193 7 69 42 400 32 64 128 256), losses := [] }

theorem u15306 : Upper (D 8) (R 8) [192,5,65,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15307 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 56 146 296 360 424 296), lower := (rows 193 7 69 56 146 32 64 128 256), losses := [] }

theorem u15307 : Upper (D 8) (R 8) [192,5,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15308 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 56 274 168 232 168 424), lower := (rows 193 7 69 56 274 32 64 128 256), losses := [] }

theorem u15308 : Upper (D 8) (R 8) [192,5,65,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15309 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 56 280 162 226 162 418), lower := (rows 193 7 69 56 280 32 64 128 256), losses := [] }

theorem u15309 : Upper (D 8) (R 8) [192,5,65,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15310 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 56 400 42 106 170 298), lower := (rows 193 7 69 56 400 32 64 128 256), losses := [] }

theorem u15310 : Upper (D 8) (R 8) [192,5,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15311 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 138 280 48 112 176 304), lower := (rows 193 7 69 138 280 32 64 128 256), losses := [] }

theorem u15311 : Upper (D 8) (R 8) [192,5,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15312 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 138 304 56 120 184 312), lower := (rows 193 7 69 138 304 32 64 128 256), losses := [] }

theorem u15312 : Upper (D 8) (R 8) [192,5,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15313 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 152 274 40 104 168 296), lower := (rows 193 7 69 152 274 32 64 128 256), losses := [] }

theorem u15313 : Upper (D 8) (R 8) [192,5,65,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15314 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 152 304 42 106 170 298), lower := (rows 193 7 69 152 304 32 64 128 256), losses := [] }

theorem u15314 : Upper (D 8) (R 8) [192,5,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15314 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15315 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 168 274 56 120 184 312), lower := (rows 193 7 69 168 274 32 64 128 256), losses := [] }

theorem u15315 : Upper (D 8) (R 8) [192,5,65,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15316 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 168 280 50 114 178 306), lower := (rows 193 7 69 168 280 32 64 128 256), losses := [] }

theorem u15316 : Upper (D 8) (R 8) [192,5,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15317 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 168 304 58 122 186 314), lower := (rows 193 7 69 168 304 32 64 128 256), losses := [] }

theorem u15317 : Upper (D 8) (R 8) [192,5,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15318 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 25 280 160 224 160 416), lower := (rows 193 7 70 25 280 32 64 128 256), losses := [] }

theorem u15318 : Upper (D 8) (R 8) [192,5,66,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15319 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 25 304 168 232 168 424), lower := (rows 193 7 70 25 304 32 64 128 256), losses := [] }

theorem u15319 : Upper (D 8) (R 8) [192,5,66,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15320 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 41 152 304 368 432 304), lower := (rows 193 7 70 41 152 32 64 128 256), losses := [] }

theorem u15320 : Upper (D 8) (R 8) [192,5,66,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15321 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 41 176 312 376 440 312), lower := (rows 193 7 70 41 176 32 64 128 256), losses := [] }

theorem u15321 : Upper (D 8) (R 8) [192,5,66,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15322 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 41 280 176 240 176 432), lower := (rows 193 7 70 41 280 32 64 128 256), losses := [] }

theorem u15322 : Upper (D 8) (R 8) [192,5,66,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15323 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 41 304 184 248 184 440), lower := (rows 193 7 70 41 304 32 64 128 256), losses := [] }

theorem u15323 : Upper (D 8) (R 8) [192,5,66,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15324 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 41 400 56 120 184 312), lower := (rows 193 7 70 41 400 32 64 128 256), losses := [] }

theorem u15324 : Upper (D 8) (R 8) [192,5,66,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15325 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 56 273 168 232 168 424), lower := (rows 193 7 70 56 273 32 64 128 256), losses := [] }

theorem u15325 : Upper (D 8) (R 8) [192,5,66,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15326 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 56 280 161 225 161 417), lower := (rows 193 7 70 56 280 32 64 128 256), losses := [] }

theorem u15326 : Upper (D 8) (R 8) [192,5,66,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15327 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 56 400 41 105 169 297), lower := (rows 193 7 70 56 400 32 64 128 256), losses := [] }

theorem u15327 : Upper (D 8) (R 8) [192,5,66,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15328 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 152 273 40 104 168 296), lower := (rows 193 7 70 152 273 32 64 128 256), losses := [] }

theorem u15328 : Upper (D 8) (R 8) [192,5,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15329 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 152 304 41 105 169 297), lower := (rows 193 7 70 152 304 32 64 128 256), losses := [] }

theorem u15329 : Upper (D 8) (R 8) [192,5,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15330 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 168 273 56 120 184 312), lower := (rows 193 7 70 168 273 32 64 128 256), losses := [] }

theorem u15330 : Upper (D 8) (R 8) [192,5,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15331 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 168 280 49 113 177 305), lower := (rows 193 7 70 168 280 32 64 128 256), losses := [] }

theorem u15331 : Upper (D 8) (R 8) [192,5,66,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15332 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 168 304 57 121 185 313), lower := (rows 193 7 70 168 304 32 64 128 256), losses := [] }

theorem u15332 : Upper (D 8) (R 8) [192,5,66,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15333 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 25 274 160 224 160 416), lower := (rows 193 7 76 25 274 32 64 128 256), losses := [] }

theorem u15333 : Upper (D 8) (R 8) [192,5,72,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15334 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 25 304 162 226 162 418), lower := (rows 193 7 76 25 304 32 64 128 256), losses := [] }

theorem u15334 : Upper (D 8) (R 8) [192,5,72,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15335 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 26 49 416 480 416 416), lower := (rows 193 7 76 26 49 32 64 128 256), losses := [] }

theorem u15335 : Upper (D 8) (R 8) [192,5,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15336 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 26 176 289 353 417 289), lower := (rows 193 7 76 26 176 32 64 128 256), losses := [] }

theorem u15336 : Upper (D 8) (R 8) [192,5,72,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15337 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 26 273 160 224 160 416), lower := (rows 193 7 76 26 273 32 64 128 256), losses := [] }

theorem u15337 : Upper (D 8) (R 8) [192,5,72,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15338 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 26 304 161 225 161 417), lower := (rows 193 7 76 26 304 32 64 128 256), losses := [] }

theorem u15338 : Upper (D 8) (R 8) [192,5,72,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15339 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 26 400 33 97 161 289), lower := (rows 193 7 76 26 400 32 64 128 256), losses := [] }

theorem u15339 : Upper (D 8) (R 8) [192,5,72,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15339 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15340 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 50 432 496 432 432), lower := (rows 193 7 76 41 50 32 64 128 256), losses := [] }

theorem u15340 : Upper (D 8) (R 8) [192,5,72,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15341 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 146 304 368 432 304), lower := (rows 193 7 76 41 146 32 64 128 256), losses := [] }

theorem u15341 : Upper (D 8) (R 8) [192,5,72,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15342 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 176 306 370 434 306), lower := (rows 193 7 76 41 176 32 64 128 256), losses := [] }

theorem u15342 : Upper (D 8) (R 8) [192,5,72,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15343 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 274 176 240 176 432), lower := (rows 193 7 76 41 274 32 64 128 256), losses := [] }

theorem u15343 : Upper (D 8) (R 8) [192,5,72,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15344 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 304 178 242 178 434), lower := (rows 193 7 76 41 304 32 64 128 256), losses := [] }

theorem u15344 : Upper (D 8) (R 8) [192,5,72,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15345 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 400 50 114 178 306), lower := (rows 193 7 76 41 400 32 64 128 256), losses := [] }

theorem u15345 : Upper (D 8) (R 8) [192,5,72,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15346 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 42 49 432 496 432 432), lower := (rows 193 7 76 42 49 32 64 128 256), losses := [] }

theorem u15346 : Upper (D 8) (R 8) [192,5,72,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15347 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 42 176 305 369 433 305), lower := (rows 193 7 76 42 176 32 64 128 256), losses := [] }

theorem u15347 : Upper (D 8) (R 8) [192,5,72,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15348 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 42 273 176 240 176 432), lower := (rows 193 7 76 42 273 32 64 128 256), losses := [] }

theorem u15348 : Upper (D 8) (R 8) [192,5,72,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15349 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 42 304 177 241 177 433), lower := (rows 193 7 76 42 304 32 64 128 256), losses := [] }

theorem u15349 : Upper (D 8) (R 8) [192,5,72,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15350 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 42 400 49 113 177 305), lower := (rows 193 7 76 42 400 32 64 128 256), losses := [] }

theorem u15350 : Upper (D 8) (R 8) [192,5,72,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15351 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 56 146 289 353 417 289), lower := (rows 193 7 76 56 146 32 64 128 256), losses := [] }

theorem u15351 : Upper (D 8) (R 8) [192,5,72,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15352 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 56 273 162 226 162 418), lower := (rows 193 7 76 56 273 32 64 128 256), losses := [] }

theorem u15352 : Upper (D 8) (R 8) [192,5,72,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15353 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 56 274 161 225 161 417), lower := (rows 193 7 76 56 274 32 64 128 256), losses := [] }

theorem u15353 : Upper (D 8) (R 8) [192,5,72,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15354 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 56 400 35 99 163 291), lower := (rows 193 7 76 56 400 32 64 128 256), losses := [] }

theorem u15354 : Upper (D 8) (R 8) [192,5,72,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15355 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 76 138 49 304 368 432 304), lower := (rows 193 7 76 138 49 32 64 128 256), losses := [] }

theorem u15355 : Upper (D 8) (R 8) [192,5,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15356 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 76 138 273 48 112 176 304), lower := (rows 193 7 76 138 273 32 64 128 256), losses := [] }

theorem u15356 : Upper (D 8) (R 8) [192,5,72,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15357 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 76 138 304 49 113 177 305), lower := (rows 193 7 76 138 304 32 64 128 256), losses := [] }

theorem u15357 : Upper (D 8) (R 8) [192,5,72,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15358 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 152 49 290 354 418 290), lower := (rows 193 7 76 152 49 32 64 128 256), losses := [] }

theorem u15358 : Upper (D 8) (R 8) [192,5,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15359 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 152 50 289 353 417 289), lower := (rows 193 7 76 152 50 32 64 128 256), losses := [] }

theorem u15359 : Upper (D 8) (R 8) [192,5,72,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15359
end Delivery.IrregularNine14.P08
