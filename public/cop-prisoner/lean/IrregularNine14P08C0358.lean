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

def b21480 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 168 407 439 471 407 407), lower := (rows 97 35 76 168 16 32 64 128 256), losses := [] }

theorem u21480 : Upper (D 8) (R 8) [96,33,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21481 : PairBound 9 := { available := 182, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 265 182 182 246 182 438), lower := (rows 97 35 76 265 16 32 64 128 256), losses := [] }

theorem u21481 : Upper (D 8) (R 8) [96,33,72,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21482 : PairBound 9 := { available := 181, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 266 181 181 245 181 437), lower := (rows 97 35 76 266 16 32 64 128 256), losses := [] }

theorem u21482 : Upper (D 8) (R 8) [96,33,72,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21483 : PairBound 9 := { available := 151, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 296 151 183 215 151 407), lower := (rows 97 35 76 296 16 32 64 128 256), losses := [] }

theorem u21483 : Upper (D 8) (R 8) [96,33,72,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21484 : PairBound 9 := { available := 183, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 392 183 183 247 183 439), lower := (rows 97 35 76 392 16 32 64 128 256), losses := [] }

theorem u21484 : Upper (D 8) (R 8) [96,33,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21485 : PairBound 9 := { available := 380, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 138 380 380 380 508 380), lower := (rows 97 35 133 138 16 32 64 128 256), losses := [] }

theorem u21485 : Upper (D 8) (R 8) [96,33,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21486 : PairBound 9 := { available := 350, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 168 350 382 350 478 350), lower := (rows 97 35 133 168 16 32 64 128 256), losses := [] }

theorem u21486 : Upper (D 8) (R 8) [96,33,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21487 : PairBound 9 := { available := 318, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 200 318 318 382 446 318), lower := (rows 97 35 133 200 16 32 64 128 256), losses := [] }

theorem u21487 : Upper (D 8) (R 8) [96,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21488 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 266 252 252 252 252 508), lower := (rows 97 35 133 266 16 32 64 128 256), losses := [] }

theorem u21488 : Upper (D 8) (R 8) [96,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21489 : PairBound 9 := { available := 250, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 268 250 250 250 250 506), lower := (rows 97 35 133 268 16 32 64 128 256), losses := [] }

theorem u21489 : Upper (D 8) (R 8) [96,33,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21490 : PairBound 9 := { available := 222, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 296 222 254 222 222 478), lower := (rows 97 35 133 296 16 32 64 128 256), losses := [] }

theorem u21490 : Upper (D 8) (R 8) [96,33,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21491 : PairBound 9 := { available := 190, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 328 190 190 254 190 446), lower := (rows 97 35 133 328 16 32 64 128 256), losses := [] }

theorem u21491 : Upper (D 8) (R 8) [96,33,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21492 : PairBound 9 := { available := 126, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 133 392 126 126 126 254 382), lower := (rows 97 35 133 392 16 32 64 128 256), losses := [] }

theorem u21492 : Upper (D 8) (R 8) [96,33,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21493 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 168 349 381 349 477 349), lower := (rows 97 35 134 168 16 32 64 128 256), losses := [] }

theorem u21493 : Upper (D 8) (R 8) [96,33,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21494 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 200 317 317 381 445 317), lower := (rows 97 35 134 200 16 32 64 128 256), losses := [] }

theorem u21494 : Upper (D 8) (R 8) [96,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21495 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 265 252 252 252 252 508), lower := (rows 97 35 134 265 16 32 64 128 256), losses := [] }

theorem u21495 : Upper (D 8) (R 8) [96,33,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21496 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 268 249 249 249 249 505), lower := (rows 97 35 134 268 16 32 64 128 256), losses := [] }

theorem u21496 : Upper (D 8) (R 8) [96,33,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21497 : PairBound 9 := { available := 221, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 296 221 253 221 221 477), lower := (rows 97 35 134 296 16 32 64 128 256), losses := [] }

theorem u21497 : Upper (D 8) (R 8) [96,33,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21498 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 328 189 189 253 189 445), lower := (rows 97 35 134 328 16 32 64 128 256), losses := [] }

theorem u21498 : Upper (D 8) (R 8) [96,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21499 : PairBound 9 := { available := 125, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 134 392 125 125 125 253 381), lower := (rows 97 35 134 392 16 32 64 128 256), losses := [] }

theorem u21499 : Upper (D 8) (R 8) [96,33,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21500 : PairBound 9 := { available := 246, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 265 246 246 246 246 502), lower := (rows 97 35 140 265 16 32 64 128 256), losses := [] }

theorem u21500 : Upper (D 8) (R 8) [96,33,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21501 : PairBound 9 := { available := 245, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 266 245 245 245 245 501), lower := (rows 97 35 140 266 16 32 64 128 256), losses := [] }

theorem u21501 : Upper (D 8) (R 8) [96,33,136,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21502 : PairBound 9 := { available := 243, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 268 243 243 243 243 499), lower := (rows 97 35 140 268 16 32 64 128 256), losses := [] }

theorem u21502 : Upper (D 8) (R 8) [96,33,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21503 : PairBound 9 := { available := 215, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 296 215 247 215 215 471), lower := (rows 97 35 140 296 16 32 64 128 256), losses := [] }

theorem u21503 : Upper (D 8) (R 8) [96,33,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21504 : PairBound 9 := { available := 183, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 140 328 183 183 247 183 439), lower := (rows 97 35 140 328 16 32 64 128 256), losses := [] }

theorem u21504 : Upper (D 8) (R 8) [96,33,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21505 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 200 287 319 351 415 287), lower := (rows 97 35 164 200 16 32 64 128 256), losses := [] }

theorem u21505 : Upper (D 8) (R 8) [96,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21506 : PairBound 9 := { available := 222, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 265 222 254 222 222 478), lower := (rows 97 35 164 265 16 32 64 128 256), losses := [] }

theorem u21506 : Upper (D 8) (R 8) [96,33,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21507 : PairBound 9 := { available := 221, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 266 221 253 221 221 477), lower := (rows 97 35 164 266 16 32 64 128 256), losses := [] }

theorem u21507 : Upper (D 8) (R 8) [96,33,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21508 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 268 219 251 219 219 475), lower := (rows 97 35 164 268 16 32 64 128 256), losses := [] }

theorem u21508 : Upper (D 8) (R 8) [96,33,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21509 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 328 159 191 223 159 415), lower := (rows 97 35 164 328 16 32 64 128 256), losses := [] }

theorem u21509 : Upper (D 8) (R 8) [96,33,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21510 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 164 392 95 127 95 223 351), lower := (rows 97 35 164 392 16 32 64 128 256), losses := [] }

theorem u21510 : Upper (D 8) (R 8) [96,33,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21511 : PairBound 9 := { available := 190, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 196 265 190 190 254 190 446), lower := (rows 97 35 196 265 16 32 64 128 256), losses := [] }

theorem u21511 : Upper (D 8) (R 8) [96,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21512 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 196 266 189 189 253 189 445), lower := (rows 97 35 196 266 16 32 64 128 256), losses := [] }

theorem u21512 : Upper (D 8) (R 8) [96,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21513 : PairBound 9 := { available := 187, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 196 268 187 187 251 187 443), lower := (rows 97 35 196 268 16 32 64 128 256), losses := [] }

theorem u21513 : Upper (D 8) (R 8) [96,33,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21514 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 196 296 159 191 223 159 415), lower := (rows 97 35 196 296 16 32 64 128 256), losses := [] }

theorem u21514 : Upper (D 8) (R 8) [96,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21515 : PairBound 9 := { available := 63, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 196 392 63 63 127 191 319), lower := (rows 97 35 196 392 16 32 64 128 256), losses := [] }

theorem u21515 : Upper (D 8) (R 8) [96,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21516 : PairBound 9 := { available := 473, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 137 473 505 473 473 473), lower := (rows 97 38 38 137 16 32 64 128 256), losses := [] }

theorem u21516 : Upper (D 8) (R 8) [96,36,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21517 : PairBound 9 := { available := 409, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 200 409 441 473 409 409), lower := (rows 97 38 38 200 16 32 64 128 256), losses := [] }

theorem u21517 : Upper (D 8) (R 8) [96,36,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21518 : PairBound 9 := { available := 217, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 265 217 249 217 217 473), lower := (rows 97 38 38 265 16 32 64 128 256), losses := [] }

theorem u21518 : Upper (D 8) (R 8) [96,36,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21519 : PairBound 9 := { available := 153, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 328 153 185 217 153 409), lower := (rows 97 38 38 328 16 32 64 128 256), losses := [] }

theorem u21519 : Upper (D 8) (R 8) [96,36,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21520 : PairBound 9 := { available := 217, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 38 392 217 249 217 217 473), lower := (rows 97 38 38 392 16 32 64 128 256), losses := [] }

theorem u21520 : Upper (D 8) (R 8) [96,36,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21521 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 74 401 433 465 401 401), lower := (rows 97 38 44 74 16 32 64 128 256), losses := [] }

theorem u21521 : Upper (D 8) (R 8) [96,36,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21522 : PairBound 9 := { available := 467, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 137 467 499 467 467 467), lower := (rows 97 38 44 137 16 32 64 128 256), losses := [] }

theorem u21522 : Upper (D 8) (R 8) [96,36,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21523 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 138 465 497 465 465 465), lower := (rows 97 38 44 138 16 32 64 128 256), losses := [] }

theorem u21523 : Upper (D 8) (R 8) [96,36,40,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21524 : PairBound 9 := { available := 403, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 200 403 435 467 403 403), lower := (rows 97 38 44 200 16 32 64 128 256), losses := [] }

theorem u21524 : Upper (D 8) (R 8) [96,36,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21525 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 265 211 243 211 211 467), lower := (rows 97 38 44 265 16 32 64 128 256), losses := [] }

theorem u21525 : Upper (D 8) (R 8) [96,36,40,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21526 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 266 209 241 209 209 465), lower := (rows 97 38 44 266 16 32 64 128 256), losses := [] }

theorem u21526 : Upper (D 8) (R 8) [96,36,40,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21527 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 328 147 179 211 147 403), lower := (rows 97 38 44 328 16 32 64 128 256), losses := [] }

theorem u21527 : Upper (D 8) (R 8) [96,36,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21528 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 44 392 211 243 211 211 467), lower := (rows 97 38 44 392 16 32 64 128 256), losses := [] }

theorem u21528 : Upper (D 8) (R 8) [96,36,40,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21529 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 74 409 425 457 393 393), lower := (rows 97 38 52 74 16 32 64 128 256), losses := [] }

theorem u21529 : Upper (D 8) (R 8) [96,36,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21530 : PairBound 9 := { available := 459, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 137 475 491 459 459 459), lower := (rows 97 38 52 137 16 32 64 128 256), losses := [] }

theorem u21530 : Upper (D 8) (R 8) [96,36,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21531 : PairBound 9 := { available := 457, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 138 473 489 457 457 457), lower := (rows 97 38 52 138 16 32 64 128 256), losses := [] }

theorem u21531 : Upper (D 8) (R 8) [96,36,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21532 : PairBound 9 := { available := 395, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 200 411 427 459 395 395), lower := (rows 97 38 52 200 16 32 64 128 256), losses := [] }

theorem u21532 : Upper (D 8) (R 8) [96,36,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21533 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 265 219 235 203 203 459), lower := (rows 97 38 52 265 16 32 64 128 256), losses := [] }

theorem u21533 : Upper (D 8) (R 8) [96,36,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21534 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 266 217 233 201 201 457), lower := (rows 97 38 52 266 16 32 64 128 256), losses := [] }

theorem u21534 : Upper (D 8) (R 8) [96,36,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21535 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 328 155 171 203 139 395), lower := (rows 97 38 52 328 16 32 64 128 256), losses := [] }

theorem u21535 : Upper (D 8) (R 8) [96,36,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21536 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 38 52 392 219 235 203 203 459), lower := (rows 97 38 52 392 16 32 64 128 256), losses := [] }

theorem u21536 : Upper (D 8) (R 8) [96,36,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21537 : PairBound 9 := { available := 442, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 137 442 442 506 442 442), lower := (rows 97 38 69 137 16 32 64 128 256), losses := [] }

theorem u21537 : Upper (D 8) (R 8) [96,36,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21538 : PairBound 9 := { available := 441, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 138 441 441 505 441 441), lower := (rows 97 38 69 138 16 32 64 128 256), losses := [] }

theorem u21538 : Upper (D 8) (R 8) [96,36,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21539 : PairBound 9 := { available := 411, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 69 168 411 443 475 411 411), lower := (rows 97 38 69 168 16 32 64 128 256), losses := [] }

theorem u21539 : Upper (D 8) (R 8) [96,36,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u21539
end Delivery.IrregularNine14.P08
