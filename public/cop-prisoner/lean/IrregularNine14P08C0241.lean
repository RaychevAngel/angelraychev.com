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

def b14460 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 152 280 225 193 193 449), lower := (rows 97 38 38 152 280 32 64 128 256), losses := [] }

theorem u14460 : Upper (D 8) (R 8) [96,36,34,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14461 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 152 336 169 201 137 393), lower := (rows 97 38 38 152 336 32 64 128 256), losses := [] }

theorem u14461 : Upper (D 8) (R 8) [96,36,34,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14462 : PairBound 9 := { available := 153, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 200 273 185 217 153 409), lower := (rows 97 38 38 200 273 32 64 128 256), losses := [] }

theorem u14462 : Upper (D 8) (R 8) [96,36,34,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14463 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 200 280 177 209 145 401), lower := (rows 97 38 38 200 280 32 64 128 256), losses := [] }

theorem u14463 : Upper (D 8) (R 8) [96,36,34,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14464 : PairBound 9 := { available := 25, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 200 400 57 89 153 281), lower := (rows 97 38 38 200 400 32 64 128 256), losses := [] }

theorem u14464 : Upper (D 8) (R 8) [96,36,34,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14465 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 74 145 433 465 401 401), lower := (rows 97 38 44 74 145 32 64 128 256), losses := [] }

theorem u14465 : Upper (D 8) (R 8) [96,36,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14466 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 74 273 177 209 145 401), lower := (rows 97 38 44 74 273 32 64 128 256), losses := [] }

theorem u14466 : Upper (D 8) (R 8) [96,36,40,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14467 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 74 400 177 209 145 401), lower := (rows 97 38 44 74 400 32 64 128 256), losses := [] }

theorem u14467 : Upper (D 8) (R 8) [96,36,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14468 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 88 145 419 451 387 387), lower := (rows 97 38 44 88 145 32 64 128 256), losses := [] }

theorem u14468 : Upper (D 8) (R 8) [96,36,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14469 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 88 146 417 449 385 385), lower := (rows 97 38 44 88 146 32 64 128 256), losses := [] }

theorem u14469 : Upper (D 8) (R 8) [96,36,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14470 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 88 273 163 195 131 387), lower := (rows 97 38 44 88 273 32 64 128 256), losses := [] }

theorem u14470 : Upper (D 8) (R 8) [96,36,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14471 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 88 274 161 193 129 385), lower := (rows 97 38 44 88 274 32 64 128 256), losses := [] }

theorem u14471 : Upper (D 8) (R 8) [96,36,40,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14472 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 88 400 163 195 131 387), lower := (rows 97 38 44 88 400 32 64 128 256), losses := [] }

theorem u14472 : Upper (D 8) (R 8) [96,36,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14473 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 82 433 465 401 401), lower := (rows 97 38 44 137 82 32 64 128 256), losses := [] }

theorem u14473 : Upper (D 8) (R 8) [96,36,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14474 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 146 369 337 465 337), lower := (rows 97 38 44 137 146 32 64 128 256), losses := [] }

theorem u14474 : Upper (D 8) (R 8) [96,36,40,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14475 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 208 307 339 403 275), lower := (rows 97 38 44 137 208 32 64 128 256), losses := [] }

theorem u14475 : Upper (D 8) (R 8) [96,36,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14476 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 273 242 210 210 466), lower := (rows 97 38 44 137 273 32 64 128 256), losses := [] }

theorem u14476 : Upper (D 8) (R 8) [96,36,40,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14477 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 274 241 209 209 465), lower := (rows 97 38 44 137 274 32 64 128 256), losses := [] }

theorem u14477 : Upper (D 8) (R 8) [96,36,40,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14478 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 336 179 211 147 403), lower := (rows 97 38 44 137 336 32 64 128 256), losses := [] }

theorem u14478 : Upper (D 8) (R 8) [96,36,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14479 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 400 115 83 211 339), lower := (rows 97 38 44 137 400 32 64 128 256), losses := [] }

theorem u14479 : Upper (D 8) (R 8) [96,36,40,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14480 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 138 145 369 337 465 337), lower := (rows 97 38 44 138 145 32 64 128 256), losses := [] }

theorem u14480 : Upper (D 8) (R 8) [96,36,40,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14481 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 138 208 305 337 401 273), lower := (rows 97 38 44 138 208 32 64 128 256), losses := [] }

theorem u14481 : Upper (D 8) (R 8) [96,36,40,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14482 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 138 273 241 209 209 465), lower := (rows 97 38 44 138 273 32 64 128 256), losses := [] }

theorem u14482 : Upper (D 8) (R 8) [96,36,40,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14483 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 138 336 177 209 145 401), lower := (rows 97 38 44 138 336 32 64 128 256), losses := [] }

theorem u14483 : Upper (D 8) (R 8) [96,36,40,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14484 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 138 400 113 81 209 337), lower := (rows 97 38 44 138 400 32 64 128 256), losses := [] }

theorem u14484 : Upper (D 8) (R 8) [96,36,40,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14485 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 152 82 417 449 385 385), lower := (rows 97 38 44 152 82 32 64 128 256), losses := [] }

theorem u14485 : Upper (D 8) (R 8) [96,36,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14486 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 152 273 227 195 195 451), lower := (rows 97 38 44 152 273 32 64 128 256), losses := [] }

theorem u14486 : Upper (D 8) (R 8) [96,36,40,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14487 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 152 274 225 193 193 449), lower := (rows 97 38 44 152 274 32 64 128 256), losses := [] }

theorem u14487 : Upper (D 8) (R 8) [96,36,40,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14488 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 152 336 163 195 131 387), lower := (rows 97 38 44 152 336 32 64 128 256), losses := [] }

theorem u14488 : Upper (D 8) (R 8) [96,36,40,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14489 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 200 145 307 339 403 275), lower := (rows 97 38 44 200 145 32 64 128 256), losses := [] }

theorem u14489 : Upper (D 8) (R 8) [96,36,40,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14490 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 200 146 305 337 401 273), lower := (rows 97 38 44 200 146 32 64 128 256), losses := [] }

theorem u14490 : Upper (D 8) (R 8) [96,36,40,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14491 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 200 273 179 211 147 403), lower := (rows 97 38 44 200 273 32 64 128 256), losses := [] }

theorem u14491 : Upper (D 8) (R 8) [96,36,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14492 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 200 274 177 209 145 401), lower := (rows 97 38 44 200 274 32 64 128 256), losses := [] }

theorem u14492 : Upper (D 8) (R 8) [96,36,40,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14493 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 200 400 51 83 147 275), lower := (rows 97 38 44 200 400 32 64 128 256), losses := [] }

theorem u14493 : Upper (D 8) (R 8) [96,36,40,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14494 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 265 82 177 209 145 401), lower := (rows 97 38 44 265 82 32 64 128 256), losses := [] }

theorem u14494 : Upper (D 8) (R 8) [96,36,40,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14495 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 265 145 242 210 210 466), lower := (rows 97 38 44 265 145 32 64 128 256), losses := [] }

theorem u14495 : Upper (D 8) (R 8) [96,36,40,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14496 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 265 146 241 209 209 465), lower := (rows 97 38 44 265 146 32 64 128 256), losses := [] }

theorem u14496 : Upper (D 8) (R 8) [96,36,40,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14497 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 265 208 179 211 147 403), lower := (rows 97 38 44 265 208 32 64 128 256), losses := [] }

theorem u14497 : Upper (D 8) (R 8) [96,36,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14498 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 266 145 241 209 209 465), lower := (rows 97 38 44 266 145 32 64 128 256), losses := [] }

theorem u14498 : Upper (D 8) (R 8) [96,36,40,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14499 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 266 208 177 209 145 401), lower := (rows 97 38 44 266 208 32 64 128 256), losses := [] }

theorem u14499 : Upper (D 8) (R 8) [96,36,40,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14500 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 280 82 161 193 129 385), lower := (rows 97 38 44 280 82 32 64 128 256), losses := [] }

theorem u14500 : Upper (D 8) (R 8) [96,36,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14501 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 280 145 227 195 195 451), lower := (rows 97 38 44 280 145 32 64 128 256), losses := [] }

theorem u14501 : Upper (D 8) (R 8) [96,36,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14502 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 280 146 225 193 193 449), lower := (rows 97 38 44 280 146 32 64 128 256), losses := [] }

theorem u14502 : Upper (D 8) (R 8) [96,36,40,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14503 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 280 208 163 195 131 387), lower := (rows 97 38 44 280 208 32 64 128 256), losses := [] }

theorem u14503 : Upper (D 8) (R 8) [96,36,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14504 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 328 145 179 211 147 403), lower := (rows 97 38 44 328 145 32 64 128 256), losses := [] }

theorem u14504 : Upper (D 8) (R 8) [96,36,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14505 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 328 146 177 209 145 401), lower := (rows 97 38 44 328 146 32 64 128 256), losses := [] }

theorem u14505 : Upper (D 8) (R 8) [96,36,40,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14506 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 392 82 177 209 145 401), lower := (rows 97 38 44 392 82 32 64 128 256), losses := [] }

theorem u14506 : Upper (D 8) (R 8) [96,36,40,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14507 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 392 145 115 83 211 339), lower := (rows 97 38 44 392 145 32 64 128 256), losses := [] }

theorem u14507 : Upper (D 8) (R 8) [96,36,40,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14508 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 392 146 113 81 209 337), lower := (rows 97 38 44 392 146 32 64 128 256), losses := [] }

theorem u14508 : Upper (D 8) (R 8) [96,36,40,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14509 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 392 208 51 83 147 275), lower := (rows 97 38 44 392 208 32 64 128 256), losses := [] }

theorem u14509 : Upper (D 8) (R 8) [96,36,40,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14510 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 145 426 458 394 394), lower := (rows 97 38 69 56 145 32 64 128 256), losses := [] }

theorem u14510 : Upper (D 8) (R 8) [96,36,65,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14511 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 146 425 457 393 393), lower := (rows 97 38 69 56 146 32 64 128 256), losses := [] }

theorem u14511 : Upper (D 8) (R 8) [96,36,65,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14512 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 152 419 451 387 387), lower := (rows 97 38 69 56 152 32 64 128 256), losses := [] }

theorem u14512 : Upper (D 8) (R 8) [96,36,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14513 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 273 170 202 138 394), lower := (rows 97 38 69 56 273 32 64 128 256), losses := [] }

theorem u14513 : Upper (D 8) (R 8) [96,36,65,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14514 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 274 169 201 137 393), lower := (rows 97 38 69 56 274 32 64 128 256), losses := [] }

theorem u14514 : Upper (D 8) (R 8) [96,36,65,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14515 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 280 163 195 131 387), lower := (rows 97 38 69 56 280 32 64 128 256), losses := [] }

theorem u14515 : Upper (D 8) (R 8) [96,36,65,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14516 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 56 400 171 203 139 395), lower := (rows 97 38 69 56 400 32 64 128 256), losses := [] }

theorem u14516 : Upper (D 8) (R 8) [96,36,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14517 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 146 312 376 440 312), lower := (rows 97 38 69 137 146 32 64 128 256), losses := [] }

theorem u14517 : Upper (D 8) (R 8) [96,36,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14518 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 176 314 346 410 282), lower := (rows 97 38 69 137 176 32 64 128 256), losses := [] }

theorem u14518 : Upper (D 8) (R 8) [96,36,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14519 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 274 184 248 184 440), lower := (rows 97 38 69 137 274 32 64 128 256), losses := [] }

theorem u14519 : Upper (D 8) (R 8) [96,36,65,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14519
end Delivery.IrregularNine14.P08
