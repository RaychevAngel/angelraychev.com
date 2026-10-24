import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0027

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 296 146 113 81 209 337), lower := (rows 97 7 140 296 146 32 64 128 256), losses := [] }

theorem u4440 : Upper (D 3) (R 3) [96,5,136,288,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4440
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4441 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 296 208 51 83 147 275), lower := (rows 97 7 140 296 208 32 64 128 256), losses := [] }

theorem u4441 : Upper (D 3) (R 3) [96,5,136,288,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4442 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 392 50 113 81 209 337), lower := (rows 97 7 140 392 50 32 64 128 256), losses := [] }

theorem u4442 : Upper (D 3) (R 3) [96,5,136,384,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4443 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 25 274 233 201 201 457), lower := (rows 97 7 164 25 274 32 64 128 256), losses := [] }

theorem u4443 : Upper (D 3) (R 3) [96,5,160,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4443
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4444 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 25 280 227 195 195 451), lower := (rows 97 7 164 25 280 32 64 128 256), losses := [] }

theorem u4444 : Upper (D 3) (R 3) [96,5,160,17,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4444
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 25 400 107 75 203 331), lower := (rows 97 7 164 25 400 32 64 128 256), losses := [] }

theorem u4445 : Upper (D 3) (R 3) [96,5,160,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4446 : PairBound 9 := { available := 329, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 145 361 329 457 329), lower := (rows 97 7 164 26 145 32 64 128 256), losses := [] }

theorem u4446 : Upper (D 3) (R 3) [96,5,160,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4446
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4447 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 152 353 321 449 321), lower := (rows 97 7 164 26 152 32 64 128 256), losses := [] }

theorem u4447 : Upper (D 3) (R 3) [96,5,160,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4447
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4448 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 208 297 329 393 265), lower := (rows 97 7 164 26 208 32 64 128 256), losses := [] }

theorem u4448 : Upper (D 3) (R 3) [96,5,160,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4448
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 273 233 201 201 457), lower := (rows 97 7 164 26 273 32 64 128 256), losses := [] }

theorem u4449 : Upper (D 3) (R 3) [96,5,160,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4449
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 280 225 193 193 449), lower := (rows 97 7 164 26 280 32 64 128 256), losses := [] }

theorem u4450 : Upper (D 3) (R 3) [96,5,160,18,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4450
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4451 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 336 169 201 137 393), lower := (rows 97 7 164 26 336 32 64 128 256), losses := [] }

theorem u4451 : Upper (D 3) (R 3) [96,5,160,18,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4451
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4452 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 400 105 73 201 329), lower := (rows 97 7 164 26 400 32 64 128 256), losses := [] }

theorem u4452 : Upper (D 3) (R 3) [96,5,160,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4452
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4453 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 74 145 313 345 409 281), lower := (rows 97 7 164 74 145 32 64 128 256), losses := [] }

theorem u4453 : Upper (D 3) (R 3) [96,5,160,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4453
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4454 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 74 152 305 337 401 273), lower := (rows 97 7 164 74 152 32 64 128 256), losses := [] }

theorem u4454 : Upper (D 3) (R 3) [96,5,160,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4454
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 74 273 185 217 153 409), lower := (rows 97 7 164 74 273 32 64 128 256), losses := [] }

theorem u4455 : Upper (D 3) (R 3) [96,5,160,66,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4455
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4456 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 74 280 177 209 145 401), lower := (rows 97 7 164 74 280 32 64 128 256), losses := [] }

theorem u4456 : Upper (D 3) (R 3) [96,5,160,66,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4457 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 74 400 57 89 153 281), lower := (rows 97 7 164 74 400 32 64 128 256), losses := [] }

theorem u4457 : Upper (D 3) (R 3) [96,5,160,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4457
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4458 : PairBound 9 := { available := 267, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 88 145 299 331 395 267), lower := (rows 97 7 164 88 145 32 64 128 256), losses := [] }

theorem u4458 : Upper (D 3) (R 3) [96,5,160,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4458
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 88 146 297 329 393 265), lower := (rows 97 7 164 88 146 32 64 128 256), losses := [] }

theorem u4459 : Upper (D 3) (R 3) [96,5,160,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4459
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4460 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 88 273 171 203 139 395), lower := (rows 97 7 164 88 273 32 64 128 256), losses := [] }

theorem u4460 : Upper (D 3) (R 3) [96,5,160,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4460
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4461 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 88 274 169 201 137 393), lower := (rows 97 7 164 88 274 32 64 128 256), losses := [] }

theorem u4461 : Upper (D 3) (R 3) [96,5,160,80,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4461
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4462 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 88 400 43 75 139 267), lower := (rows 97 7 164 88 400 32 64 128 256), losses := [] }

theorem u4462 : Upper (D 3) (R 3) [96,5,160,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4462
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4463 : PairBound 9 := { available := 90, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 137 273 122 90 218 346), lower := (rows 97 7 164 137 273 32 64 128 256), losses := [] }

theorem u4463 : Upper (D 3) (R 3) [96,5,160,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4463
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4464 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 137 274 121 89 217 345), lower := (rows 97 7 164 137 274 32 64 128 256), losses := [] }

theorem u4464 : Upper (D 3) (R 3) [96,5,160,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4464
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4465 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 137 280 115 83 211 339), lower := (rows 97 7 164 137 280 32 64 128 256), losses := [] }

theorem u4465 : Upper (D 3) (R 3) [96,5,160,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4465
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 137 336 59 91 155 283), lower := (rows 97 7 164 137 336 32 64 128 256), losses := [] }

theorem u4466 : Upper (D 3) (R 3) [96,5,160,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 138 273 121 89 217 345), lower := (rows 97 7 164 138 273 32 64 128 256), losses := [] }

theorem u4467 : Upper (D 3) (R 3) [96,5,160,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4467
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 138 280 113 81 209 337), lower := (rows 97 7 164 138 280 32 64 128 256), losses := [] }

theorem u4468 : Upper (D 3) (R 3) [96,5,160,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4468
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 138 336 57 89 153 281), lower := (rows 97 7 164 138 336 32 64 128 256), losses := [] }

theorem u4469 : Upper (D 3) (R 3) [96,5,160,130,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4469
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 152 273 107 75 203 331), lower := (rows 97 7 164 152 273 32 64 128 256), losses := [] }

theorem u4470 : Upper (D 3) (R 3) [96,5,160,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4470
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4471 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 152 274 105 73 201 329), lower := (rows 97 7 164 152 274 32 64 128 256), losses := [] }

theorem u4471 : Upper (D 3) (R 3) [96,5,160,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4471
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4472 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 152 280 99 67 195 323), lower := (rows 97 7 164 152 280 32 64 128 256), losses := [] }

theorem u4472 : Upper (D 3) (R 3) [96,5,160,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4472
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 152 336 43 75 139 267), lower := (rows 97 7 164 152 336 32 64 128 256), losses := [] }

theorem u4473 : Upper (D 3) (R 3) [96,5,160,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4473
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 200 273 59 91 155 283), lower := (rows 97 7 164 200 273 32 64 128 256), losses := [] }

theorem u4474 : Upper (D 3) (R 3) [96,5,160,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4474
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4475 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 200 274 57 89 153 281), lower := (rows 97 7 164 200 274 32 64 128 256), losses := [] }

theorem u4475 : Upper (D 3) (R 3) [96,5,160,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4475
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4476 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 200 280 51 83 147 275), lower := (rows 97 7 164 200 280 32 64 128 256), losses := [] }

theorem u4476 : Upper (D 3) (R 3) [96,5,160,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4476
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4477 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 145 232 232 232 488), lower := (rows 97 7 261 26 145 32 64 128 256), losses := [] }

theorem u4477 : Upper (D 3) (R 3) [96,5,257,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4477
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 152 225 225 225 481), lower := (rows 97 7 261 26 152 32 64 128 256), losses := [] }

theorem u4478 : Upper (D 3) (R 3) [96,5,257,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4478
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4479 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 26 176 233 201 201 457), lower := (rows 97 7 261 26 176 32 64 128 256), losses := [] }

theorem u4479 : Upper (D 3) (R 3) [96,5,257,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4479
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4480 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 88 177 209 145 401), lower := (rows 97 7 261 42 88 32 64 128 256), losses := [] }

theorem u4480 : Upper (D 3) (R 3) [96,5,257,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4480
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4481 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 145 248 216 216 472), lower := (rows 97 7 261 42 145 32 64 128 256), losses := [] }

theorem u4481 : Upper (D 3) (R 3) [96,5,257,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4481
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4482 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 152 241 209 209 465), lower := (rows 97 7 261 42 152 32 64 128 256), losses := [] }

theorem u4482 : Upper (D 3) (R 3) [96,5,257,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4482
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4483 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 42 208 185 217 153 409), lower := (rows 97 7 261 42 208 32 64 128 256), losses := [] }

theorem u4483 : Upper (D 3) (R 3) [96,5,257,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4483
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4484 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 145 234 202 202 458), lower := (rows 97 7 261 56 145 32 64 128 256), losses := [] }

theorem u4484 : Upper (D 3) (R 3) [96,5,257,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4484
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4485 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 146 233 201 201 457), lower := (rows 97 7 261 56 146 32 64 128 256), losses := [] }

theorem u4485 : Upper (D 3) (R 3) [96,5,257,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4485
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4486 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 56 208 171 203 139 395), lower := (rows 97 7 261 56 208 32 64 128 256), losses := [] }

theorem u4486 : Upper (D 3) (R 3) [96,5,257,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4486
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4487 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 137 146 120 120 248 376), lower := (rows 97 7 261 137 146 32 64 128 256), losses := [] }

theorem u4487 : Upper (D 3) (R 3) [96,5,257,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4487
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4488 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 137 176 122 90 218 346), lower := (rows 97 7 261 137 176 32 64 128 256), losses := [] }

theorem u4488 : Upper (D 3) (R 3) [96,5,257,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4488
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4489 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 138 176 121 89 217 345), lower := (rows 97 7 261 138 176 32 64 128 256), losses := [] }

theorem u4489 : Upper (D 3) (R 3) [96,5,257,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4489
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4490 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 261 168 208 59 91 155 283), lower := (rows 97 7 261 168 208 32 64 128 256), losses := [] }

theorem u4490 : Upper (D 3) (R 3) [96,5,257,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4490
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4491 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 262 41 88 177 209 145 401), lower := (rows 97 7 262 41 88 32 64 128 256), losses := [] }

theorem u4491 : Upper (D 3) (R 3) [96,5,258,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4492 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 262 41 145 248 216 216 472), lower := (rows 97 7 262 41 145 32 64 128 256), losses := [] }

theorem u4492 : Upper (D 3) (R 3) [96,5,258,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4492
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4493 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 262 41 152 241 209 209 465), lower := (rows 97 7 262 41 152 32 64 128 256), losses := [] }

theorem u4493 : Upper (D 3) (R 3) [96,5,258,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4493
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4494 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 262 41 208 185 217 153 409), lower := (rows 97 7 262 41 208 32 64 128 256), losses := [] }

theorem u4494 : Upper (D 3) (R 3) [96,5,258,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4494
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4495 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 56 88 161 193 129 385), lower := (rows 97 7 262 56 88 32 64 128 256), losses := [] }

theorem u4495 : Upper (D 3) (R 3) [96,5,258,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4495
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4496 : Route 9 := (fun mask => (mask,id))

def c4496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4496 : Upper (D 3) (R 3) [96,5,258,48,129] 13 := by
  apply FastRouting.sound _ _ [96,5,258,48,129] 13 (by decide) (choices 1) [1,8,64,128] r4496 c4496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1654
  · exact u1655
  · exact u1656
  · exact u1657

def b4497 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 262 56 152 225 193 193 449), lower := (rows 97 7 262 56 152 32 64 128 256), losses := [] }

theorem u4497 : Upper (D 3) (R 3) [96,5,258,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4497
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4498 : Route 9 := (fun mask => (mask,id))

def c4498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4498 : Upper (D 3) (R 3) [96,5,258,48,192] 13 := by
  apply FastRouting.sound _ _ [96,5,258,48,192] 13 (by decide) (choices 1) [1,8,128] r4498 c4498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1658
  · exact u1659
  · exact u1660

def b4499 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 262 104 145 185 217 153 409), lower := (rows 97 7 262 104 145 32 64 128 256), losses := [] }

theorem u4499 : Upper (D 3) (R 3) [96,5,258,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4499
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4499
end Delivery.IrregularNine14.P03
