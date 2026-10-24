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

def b14400 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 265 146 180 244 180 436), lower := (rows 97 35 76 265 146 32 64 128 256), losses := [] }

theorem u14400 : Upper (D 8) (R 8) [96,33,72,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14401 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 265 148 178 242 178 434), lower := (rows 97 35 76 265 148 32 64 128 256), losses := [] }

theorem u14401 : Upper (D 8) (R 8) [96,33,72,257,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14402 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 265 176 182 214 150 406), lower := (rows 97 35 76 265 176 32 64 128 256), losses := [] }

theorem u14402 : Upper (D 8) (R 8) [96,33,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14403 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 266 145 180 244 180 436), lower := (rows 97 35 76 266 145 32 64 128 256), losses := [] }

theorem u14403 : Upper (D 8) (R 8) [96,33,72,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14404 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 266 148 177 241 177 433), lower := (rows 97 35 76 266 148 32 64 128 256), losses := [] }

theorem u14404 : Upper (D 8) (R 8) [96,33,72,258,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14405 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 266 176 181 213 149 405), lower := (rows 97 35 76 266 176 32 64 128 256), losses := [] }

theorem u14405 : Upper (D 8) (R 8) [96,33,72,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14406 : PairBound 9 := { available := 166, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 280 145 166 230 166 422), lower := (rows 97 35 76 280 145 32 64 128 256), losses := [] }

theorem u14406 : Upper (D 8) (R 8) [96,33,72,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14406 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14407 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 280 146 165 229 165 421), lower := (rows 97 35 76 280 146 32 64 128 256), losses := [] }

theorem u14407 : Upper (D 8) (R 8) [96,33,72,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14407 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14408 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 280 176 167 199 135 391), lower := (rows 97 35 76 280 176 32 64 128 256), losses := [] }

theorem u14408 : Upper (D 8) (R 8) [96,33,72,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14409 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 296 145 182 214 150 406), lower := (rows 97 35 76 296 145 32 64 128 256), losses := [] }

theorem u14409 : Upper (D 8) (R 8) [96,33,72,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14409 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14410 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 296 146 181 213 149 405), lower := (rows 97 35 76 296 146 32 64 128 256), losses := [] }

theorem u14410 : Upper (D 8) (R 8) [96,33,72,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14411 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 296 148 179 211 147 403), lower := (rows 97 35 76 296 148 32 64 128 256), losses := [] }

theorem u14411 : Upper (D 8) (R 8) [96,33,72,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14412 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 392 145 54 118 182 310), lower := (rows 97 35 76 392 145 32 64 128 256), losses := [] }

theorem u14412 : Upper (D 8) (R 8) [96,33,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14412 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14413 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 392 146 53 117 181 309), lower := (rows 97 35 76 392 146 32 64 128 256), losses := [] }

theorem u14413 : Upper (D 8) (R 8) [96,33,72,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14414 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 392 176 55 87 151 279), lower := (rows 97 35 76 392 176 32 64 128 256), losses := [] }

theorem u14414 : Upper (D 8) (R 8) [96,33,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14415 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 138 276 120 120 248 376), lower := (rows 97 35 133 138 276 32 64 128 256), losses := [] }

theorem u14415 : Upper (D 8) (R 8) [96,33,129,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14415 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14416 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 138 280 116 116 244 372), lower := (rows 97 35 133 138 280 32 64 128 256), losses := [] }

theorem u14416 : Upper (D 8) (R 8) [96,33,129,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14417 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 138 304 124 92 220 348), lower := (rows 97 35 133 138 304 32 64 128 256), losses := [] }

theorem u14417 : Upper (D 8) (R 8) [96,33,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14418 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 138 336 60 124 188 316), lower := (rows 97 35 133 138 336 32 64 128 256), losses := [] }

theorem u14418 : Upper (D 8) (R 8) [96,33,129,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14419 : PairBound 9 := { available := 108, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 152 274 108 108 236 364), lower := (rows 97 35 133 152 274 32 64 128 256), losses := [] }

theorem u14419 : Upper (D 8) (R 8) [96,33,129,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14420 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 152 304 110 78 206 334), lower := (rows 97 35 133 152 304 32 64 128 256), losses := [] }

theorem u14420 : Upper (D 8) (R 8) [96,33,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14421 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 152 336 46 110 174 302), lower := (rows 97 35 133 152 336 32 64 128 256), losses := [] }

theorem u14421 : Upper (D 8) (R 8) [96,33,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14422 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 168 274 124 92 220 348), lower := (rows 97 35 133 168 274 32 64 128 256), losses := [] }

theorem u14422 : Upper (D 8) (R 8) [96,33,129,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14423 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 168 276 122 90 218 346), lower := (rows 97 35 133 168 276 32 64 128 256), losses := [] }

theorem u14423 : Upper (D 8) (R 8) [96,33,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14424 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 168 280 118 86 214 342), lower := (rows 97 35 133 168 280 32 64 128 256), losses := [] }

theorem u14424 : Upper (D 8) (R 8) [96,33,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14425 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 168 336 62 94 158 286), lower := (rows 97 35 133 168 336 32 64 128 256), losses := [] }

theorem u14425 : Upper (D 8) (R 8) [96,33,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14426 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 200 274 60 124 188 316), lower := (rows 97 35 133 200 274 32 64 128 256), losses := [] }

theorem u14426 : Upper (D 8) (R 8) [96,33,129,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14426 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14427 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 200 276 58 122 186 314), lower := (rows 97 35 133 200 276 32 64 128 256), losses := [] }

theorem u14427 : Upper (D 8) (R 8) [96,33,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14428 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 200 280 54 118 182 310), lower := (rows 97 35 133 200 280 32 64 128 256), losses := [] }

theorem u14428 : Upper (D 8) (R 8) [96,33,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14429 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 200 304 62 94 158 286), lower := (rows 97 35 133 200 304 32 64 128 256), losses := [] }

theorem u14429 : Upper (D 8) (R 8) [96,33,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14430 : PairBound 9 := { available := 108, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 152 273 108 108 236 364), lower := (rows 97 35 134 152 273 32 64 128 256), losses := [] }

theorem u14430 : Upper (D 8) (R 8) [96,33,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14431 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 152 304 109 77 205 333), lower := (rows 97 35 134 152 304 32 64 128 256), losses := [] }

theorem u14431 : Upper (D 8) (R 8) [96,33,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14432 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 152 336 45 109 173 301), lower := (rows 97 35 134 152 336 32 64 128 256), losses := [] }

theorem u14432 : Upper (D 8) (R 8) [96,33,130,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14433 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 168 273 124 92 220 348), lower := (rows 97 35 134 168 273 32 64 128 256), losses := [] }

theorem u14433 : Upper (D 8) (R 8) [96,33,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14434 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 168 276 121 89 217 345), lower := (rows 97 35 134 168 276 32 64 128 256), losses := [] }

theorem u14434 : Upper (D 8) (R 8) [96,33,130,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14435 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 168 280 117 85 213 341), lower := (rows 97 35 134 168 280 32 64 128 256), losses := [] }

theorem u14435 : Upper (D 8) (R 8) [96,33,130,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14436 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 168 336 61 93 157 285), lower := (rows 97 35 134 168 336 32 64 128 256), losses := [] }

theorem u14436 : Upper (D 8) (R 8) [96,33,130,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14437 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 200 273 60 124 188 316), lower := (rows 97 35 134 200 273 32 64 128 256), losses := [] }

theorem u14437 : Upper (D 8) (R 8) [96,33,130,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14438 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 200 276 57 121 185 313), lower := (rows 97 35 134 200 276 32 64 128 256), losses := [] }

theorem u14438 : Upper (D 8) (R 8) [96,33,130,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14439 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 200 280 53 117 181 309), lower := (rows 97 35 134 200 280 32 64 128 256), losses := [] }

theorem u14439 : Upper (D 8) (R 8) [96,33,130,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14440 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 200 304 61 93 157 285), lower := (rows 97 35 134 200 304 32 64 128 256), losses := [] }

theorem u14440 : Upper (D 8) (R 8) [96,33,130,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14441 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 265 176 118 86 214 342), lower := (rows 97 35 140 265 176 32 64 128 256), losses := [] }

theorem u14441 : Upper (D 8) (R 8) [96,33,136,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14442 : PairBound 9 := { available := 54, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 265 208 54 118 182 310), lower := (rows 97 35 140 265 208 32 64 128 256), losses := [] }

theorem u14442 : Upper (D 8) (R 8) [96,33,136,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14443 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 266 176 117 85 213 341), lower := (rows 97 35 140 266 176 32 64 128 256), losses := [] }

theorem u14443 : Upper (D 8) (R 8) [96,33,136,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14444 : PairBound 9 := { available := 53, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 266 208 53 117 181 309), lower := (rows 97 35 140 266 208 32 64 128 256), losses := [] }

theorem u14444 : Upper (D 8) (R 8) [96,33,136,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14445 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 296 208 55 87 151 279), lower := (rows 97 35 140 296 208 32 64 128 256), losses := [] }

theorem u14445 : Upper (D 8) (R 8) [96,33,136,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14446 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 328 176 55 87 151 279), lower := (rows 97 35 140 328 176 32 64 128 256), losses := [] }

theorem u14446 : Upper (D 8) (R 8) [96,33,136,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14447 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 200 273 62 94 158 286), lower := (rows 97 35 164 200 273 32 64 128 256), losses := [] }

theorem u14447 : Upper (D 8) (R 8) [96,33,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14448 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 200 274 61 93 157 285), lower := (rows 97 35 164 200 274 32 64 128 256), losses := [] }

theorem u14448 : Upper (D 8) (R 8) [96,33,160,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14449 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 200 276 59 91 155 283), lower := (rows 97 35 164 200 276 32 64 128 256), losses := [] }

theorem u14449 : Upper (D 8) (R 8) [96,33,160,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14450 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 200 280 55 87 151 279), lower := (rows 97 35 164 200 280 32 64 128 256), losses := [] }

theorem u14450 : Upper (D 8) (R 8) [96,33,160,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14451 : PairBound 9 := { available := 393, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 88 145 425 457 393 393), lower := (rows 97 38 38 88 145 32 64 128 256), losses := [] }

theorem u14451 : Upper (D 8) (R 8) [96,36,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14452 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 88 273 169 201 137 393), lower := (rows 97 38 38 88 273 32 64 128 256), losses := [] }

theorem u14452 : Upper (D 8) (R 8) [96,36,34,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14453 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 88 400 169 201 137 393), lower := (rows 97 38 38 88 400 32 64 128 256), losses := [] }

theorem u14453 : Upper (D 8) (R 8) [96,36,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14454 : PairBound 9 := { available := 281, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 137 208 313 345 409 281), lower := (rows 97 38 38 137 208 32 64 128 256), losses := [] }

theorem u14454 : Upper (D 8) (R 8) [96,36,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14455 : PairBound 9 := { available := 216, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 137 273 248 216 216 472), lower := (rows 97 38 38 137 273 32 64 128 256), losses := [] }

theorem u14455 : Upper (D 8) (R 8) [96,36,34,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14456 : PairBound 9 := { available := 209, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 137 280 241 209 209 465), lower := (rows 97 38 38 137 280 32 64 128 256), losses := [] }

theorem u14456 : Upper (D 8) (R 8) [96,36,34,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14457 : PairBound 9 := { available := 153, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 137 336 185 217 153 409), lower := (rows 97 38 38 137 336 32 64 128 256), losses := [] }

theorem u14457 : Upper (D 8) (R 8) [96,36,34,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14458 : PairBound 9 := { available := 89, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 137 400 121 89 217 345), lower := (rows 97 38 38 137 400 32 64 128 256), losses := [] }

theorem u14458 : Upper (D 8) (R 8) [96,36,34,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14459 : PairBound 9 := { available := 201, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 152 273 233 201 201 457), lower := (rows 97 38 38 152 273 32 64 128 256), losses := [] }

theorem u14459 : Upper (D 8) (R 8) [96,36,34,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14459
end Delivery.IrregularNine14.P08
