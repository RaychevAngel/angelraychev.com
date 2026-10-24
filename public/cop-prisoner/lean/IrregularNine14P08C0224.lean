import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0074

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13440 : PairBound 9 := { available := 298, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 145 298 362 426 298), lower := (rows 97 7 196 56 145 32 64 128 256), losses := [] }

theorem u13440 : Upper (D 8) (R 8) [96,5,192,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13441 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 146 297 361 425 297), lower := (rows 97 7 196 56 146 32 64 128 256), losses := [] }

theorem u13441 : Upper (D 8) (R 8) [96,5,192,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13442 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 152 291 355 419 291), lower := (rows 97 7 196 56 152 32 64 128 256), losses := [] }

theorem u13442 : Upper (D 8) (R 8) [96,5,192,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13443 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 273 170 234 170 426), lower := (rows 97 7 196 56 273 32 64 128 256), losses := [] }

theorem u13443 : Upper (D 8) (R 8) [96,5,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13444 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 274 169 233 169 425), lower := (rows 97 7 196 56 274 32 64 128 256), losses := [] }

theorem u13444 : Upper (D 8) (R 8) [96,5,192,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13445 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 280 163 227 163 419), lower := (rows 97 7 196 56 280 32 64 128 256), losses := [] }

theorem u13445 : Upper (D 8) (R 8) [96,5,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13446 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 56 400 43 107 171 299), lower := (rows 97 7 196 56 400 32 64 128 256), losses := [] }

theorem u13446 : Upper (D 8) (R 8) [96,5,192,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13447 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 137 274 56 120 184 312), lower := (rows 97 7 196 137 274 32 64 128 256), losses := [] }

theorem u13447 : Upper (D 8) (R 8) [96,5,192,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13448 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 137 280 50 114 178 306), lower := (rows 97 7 196 137 280 32 64 128 256), losses := [] }

theorem u13448 : Upper (D 8) (R 8) [96,5,192,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13449 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 137 304 58 122 186 314), lower := (rows 97 7 196 137 304 32 64 128 256), losses := [] }

theorem u13449 : Upper (D 8) (R 8) [96,5,192,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13450 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 138 273 56 120 184 312), lower := (rows 97 7 196 138 273 32 64 128 256), losses := [] }

theorem u13450 : Upper (D 8) (R 8) [96,5,192,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13451 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 138 280 49 113 177 305), lower := (rows 97 7 196 138 280 32 64 128 256), losses := [] }

theorem u13451 : Upper (D 8) (R 8) [96,5,192,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13452 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 138 304 57 121 185 313), lower := (rows 97 7 196 138 304 32 64 128 256), losses := [] }

theorem u13452 : Upper (D 8) (R 8) [96,5,192,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13453 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 152 273 42 106 170 298), lower := (rows 97 7 196 152 273 32 64 128 256), losses := [] }

theorem u13453 : Upper (D 8) (R 8) [96,5,192,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13454 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 152 274 41 105 169 297), lower := (rows 97 7 196 152 274 32 64 128 256), losses := [] }

theorem u13454 : Upper (D 8) (R 8) [96,5,192,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13455 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 152 280 35 99 163 291), lower := (rows 97 7 196 152 280 32 64 128 256), losses := [] }

theorem u13455 : Upper (D 8) (R 8) [96,5,192,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13456 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 152 304 43 107 171 299), lower := (rows 97 7 196 152 304 32 64 128 256), losses := [] }

theorem u13456 : Upper (D 8) (R 8) [96,5,192,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13457 : PairBound 9 := { available := 58, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 168 273 58 122 186 314), lower := (rows 97 7 196 168 273 32 64 128 256), losses := [] }

theorem u13457 : Upper (D 8) (R 8) [96,5,192,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13458 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 168 274 57 121 185 313), lower := (rows 97 7 196 168 274 32 64 128 256), losses := [] }

theorem u13458 : Upper (D 8) (R 8) [96,5,192,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13459 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 168 280 51 115 179 307), lower := (rows 97 7 196 168 280 32 64 128 256), losses := [] }

theorem u13459 : Upper (D 8) (R 8) [96,5,192,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13460 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 196 168 304 59 91 155 283), lower := (rows 97 7 196 168 304 32 64 128 256), losses := [] }

theorem u13460 : Upper (D 8) (R 8) [96,5,192,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13461 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 56 224 224 224 480), lower := (rows 97 7 261 26 56 32 64 128 256), losses := [] }

theorem u13461 : Upper (D 8) (R 8) [96,5,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13462 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 152 224 224 224 480), lower := (rows 97 7 261 26 152 32 64 128 256), losses := [] }

theorem u13462 : Upper (D 8) (R 8) [96,5,257,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13463 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 176 232 232 232 488), lower := (rows 97 7 261 26 176 32 64 128 256), losses := [] }

theorem u13463 : Upper (D 8) (R 8) [96,5,257,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13464 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 208 168 232 168 424), lower := (rows 97 7 261 26 208 32 64 128 256), losses := [] }

theorem u13464 : Upper (D 8) (R 8) [96,5,257,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13465 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 88 176 240 176 432), lower := (rows 97 7 261 42 88 32 64 128 256), losses := [] }

theorem u13465 : Upper (D 8) (R 8) [96,5,257,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13466 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 152 240 240 240 496), lower := (rows 97 7 261 42 152 32 64 128 256), losses := [] }

theorem u13466 : Upper (D 8) (R 8) [96,5,257,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13467 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 176 248 216 216 472), lower := (rows 97 7 261 42 176 32 64 128 256), losses := [] }

theorem u13467 : Upper (D 8) (R 8) [96,5,257,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13468 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 208 184 248 184 440), lower := (rows 97 7 261 42 208 32 64 128 256), losses := [] }

theorem u13468 : Upper (D 8) (R 8) [96,5,257,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13469 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 82 168 232 168 424), lower := (rows 97 7 261 56 82 32 64 128 256), losses := [] }

theorem u13469 : Upper (D 8) (R 8) [96,5,257,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13470 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 146 232 232 232 488), lower := (rows 97 7 261 56 146 32 64 128 256), losses := [] }

theorem u13470 : Upper (D 8) (R 8) [96,5,257,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13471 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 152 226 226 226 482), lower := (rows 97 7 261 56 152 32 64 128 256), losses := [] }

theorem u13471 : Upper (D 8) (R 8) [96,5,257,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13472 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 208 170 234 170 426), lower := (rows 97 7 261 56 208 32 64 128 256), losses := [] }

theorem u13472 : Upper (D 8) (R 8) [96,5,257,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13473 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 74 152 176 240 176 432), lower := (rows 97 7 261 74 152 32 64 128 256), losses := [] }

theorem u13473 : Upper (D 8) (R 8) [96,5,257,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13474 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 74 176 184 248 184 440), lower := (rows 97 7 261 74 176 32 64 128 256), losses := [] }

theorem u13474 : Upper (D 8) (R 8) [96,5,257,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13475 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 88 146 168 232 168 424), lower := (rows 97 7 261 88 146 32 64 128 256), losses := [] }

theorem u13475 : Upper (D 8) (R 8) [96,5,257,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13476 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 88 176 170 234 170 426), lower := (rows 97 7 261 88 176 32 64 128 256), losses := [] }

theorem u13476 : Upper (D 8) (R 8) [96,5,257,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13477 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 138 176 120 120 248 376), lower := (rows 97 7 261 138 176 32 64 128 256), losses := [] }

theorem u13477 : Upper (D 8) (R 8) [96,5,257,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13478 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 138 208 56 120 184 312), lower := (rows 97 7 261 138 208 32 64 128 256), losses := [] }

theorem u13478 : Upper (D 8) (R 8) [96,5,257,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13479 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 168 208 58 122 186 314), lower := (rows 97 7 261 168 208 32 64 128 256), losses := [] }

theorem u13479 : Upper (D 8) (R 8) [96,5,257,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13480 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 262 41 56 240 208 208 464), lower := (rows 97 7 262 41 56 32 64 128 256), losses := [] }

theorem u13480 : Upper (D 8) (R 8) [96,5,258,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13481 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 8, targets := 128 }], pairs := [(3,7)], upper := (rows 97 7 262 41 88 176 240 176 432), lower := (rows 97 7 262 41 88 32 64 128 256), losses := [] }

theorem u13481 : Upper (D 8) (R 8) [96,5,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13482 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 262 41 152 240 240 240 496), lower := (rows 97 7 262 41 152 32 64 128 256), losses := [] }

theorem u13482 : Upper (D 8) (R 8) [96,5,258,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13483 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 262 41 176 248 216 216 472), lower := (rows 97 7 262 41 176 32 64 128 256), losses := [] }

theorem u13483 : Upper (D 8) (R 8) [96,5,258,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13484 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 262 41 208 184 248 184 440), lower := (rows 97 7 262 41 208 32 64 128 256), losses := [] }

theorem u13484 : Upper (D 8) (R 8) [96,5,258,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13485 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 56 225 193 193 449), lower := (rows 97 7 262 56 56 32 64 128 256), losses := [] }

theorem u13485 : Upper (D 8) (R 8) [96,5,258,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13486 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 56 81 168 232 168 424), lower := (rows 97 7 262 56 81 32 64 128 256), losses := [] }

theorem u13486 : Upper (D 8) (R 8) [96,5,258,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13487 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 88 161 225 161 417), lower := (rows 97 7 262 56 88 32 64 128 256), losses := [] }

theorem u13487 : Upper (D 8) (R 8) [96,5,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13488 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 112 169 201 137 393), lower := (rows 97 7 262 56 112 32 64 128 256), losses := [] }

theorem u13488 : Upper (D 8) (R 8) [96,5,258,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13489 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 145 232 232 232 488), lower := (rows 97 7 262 56 145 32 64 128 256), losses := [] }

theorem u13489 : Upper (D 8) (R 8) [96,5,258,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13490 : Route 9 := (fun mask => (mask,id))

def c13490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13490 : Upper (D 8) (R 8) [96,5,258,48,136] 13 := by
  apply FastRouting.sound _ _ [96,5,258,48,136] 13 (by decide) (choices 1) [1,64,128] r13490 c13490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4470
  · exact u4471
  · exact u4472

def b13491 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 176 233 201 201 457), lower := (rows 97 7 262 56 176 32 64 128 256), losses := [] }

theorem u13491 : Upper (D 8) (R 8) [96,5,258,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13492 : Route 9 := (fun mask => (mask,id))

def c13492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13492 : Upper (D 8) (R 8) [96,5,258,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,258,48,192] 13 (by decide) (choices 1) [1,8,128] r13492 c13492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4473
  · exact u4474
  · exact u4475

def b13493 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 73 152 176 240 176 432), lower := (rows 97 7 262 73 152 32 64 128 256), losses := [] }

theorem u13493 : Upper (D 8) (R 8) [96,5,258,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13494 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 73 176 184 248 184 440), lower := (rows 97 7 262 73 176 32 64 128 256), losses := [] }

theorem u13494 : Upper (D 8) (R 8) [96,5,258,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13495 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 88 145 168 232 168 424), lower := (rows 97 7 262 88 145 32 64 128 256), losses := [] }

theorem u13495 : Upper (D 8) (R 8) [96,5,258,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13496 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 88 152 161 225 161 417), lower := (rows 97 7 262 88 152 32 64 128 256), losses := [] }

theorem u13496 : Upper (D 8) (R 8) [96,5,258,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13497 : Route 9 := (fun mask => (mask,id))

def c13497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13497 : Upper (D 8) (R 8) [96,5,258,80,160] 13 := by
  apply FastRouting.sound _ _ [96,5,258,80,160] 13 (by decide) (choices 1) [1,8,128] r13497 c13497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4476
  · exact u4477
  · exact u4478

def b13498 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 104 152 177 241 177 433), lower := (rows 97 7 262 104 152 32 64 128 256), losses := [] }

theorem u13498 : Upper (D 8) (R 8) [96,5,258,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13499 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 104 176 185 217 153 409), lower := (rows 97 7 262 104 176 32 64 128 256), losses := [] }

theorem u13499 : Upper (D 8) (R 8) [96,5,258,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13499
end Delivery.IrregularNine14.P08
