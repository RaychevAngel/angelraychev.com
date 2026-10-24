import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0034

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5400 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 25 82 225 193 193 449), lower := (rows 289 7 44 25 82 32 64 128 256), losses := [] }

theorem u5400 : Upper (D 3) (R 3) [288,5,40,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5400
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5401 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 25 208 227 195 195 451), lower := (rows 289 7 44 25 208 32 64 128 256), losses := [] }

theorem u5401 : Upper (D 3) (R 3) [288,5,40,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5401
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5402 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 26 81 225 193 193 449), lower := (rows 289 7 44 26 81 32 64 128 256), losses := [] }

theorem u5402 : Upper (D 3) (R 3) [288,5,40,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5402
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5403 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 26 208 225 193 193 449), lower := (rows 289 7 44 26 208 32 64 128 256), losses := [] }

theorem u5403 : Upper (D 3) (R 3) [288,5,40,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5403
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5404 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 73 82 177 209 145 401), lower := (rows 289 7 44 73 82 32 64 128 256), losses := [] }

theorem u5404 : Upper (D 3) (R 3) [288,5,40,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5404
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5405 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 73 145 242 210 210 466), lower := (rows 289 7 44 73 145 32 64 128 256), losses := [] }

theorem u5405 : Upper (D 3) (R 3) [288,5,40,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5405
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5406 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 73 146 241 209 209 465), lower := (rows 289 7 44 73 146 32 64 128 256), losses := [] }

theorem u5406 : Upper (D 3) (R 3) [288,5,40,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5406
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5407 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 73 208 179 211 147 403), lower := (rows 289 7 44 73 208 32 64 128 256), losses := [] }

theorem u5407 : Upper (D 3) (R 3) [288,5,40,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5407
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5408 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 74 81 177 209 145 401), lower := (rows 289 7 44 74 81 32 64 128 256), losses := [] }

theorem u5408 : Upper (D 3) (R 3) [288,5,40,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5408
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5409 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 74 145 241 209 209 465), lower := (rows 289 7 44 74 145 32 64 128 256), losses := [] }

theorem u5409 : Upper (D 3) (R 3) [288,5,40,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5409
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5410 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 74 208 177 209 145 401), lower := (rows 289 7 44 74 208 32 64 128 256), losses := [] }

theorem u5410 : Upper (D 3) (R 3) [288,5,40,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5410
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5411 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 88 145 227 195 195 451), lower := (rows 289 7 44 88 145 32 64 128 256), losses := [] }

theorem u5411 : Upper (D 3) (R 3) [288,5,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5411
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5412 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 88 146 225 193 193 449), lower := (rows 289 7 44 88 146 32 64 128 256), losses := [] }

theorem u5412 : Upper (D 3) (R 3) [288,5,40,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5412
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5413 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 200 81 179 211 147 403), lower := (rows 289 7 44 200 81 32 64 128 256), losses := [] }

theorem u5413 : Upper (D 3) (R 3) [288,5,40,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5413
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5414 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 200 82 177 209 145 401), lower := (rows 289 7 44 200 82 32 64 128 256), losses := [] }

theorem u5414 : Upper (D 3) (R 3) [288,5,40,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5414
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5415 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 25 82 168 232 168 424), lower := (rows 289 7 69 25 82 32 64 128 256), losses := [] }

theorem u5415 : Upper (D 3) (R 3) [288,5,65,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5415
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5416 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 25 88 162 226 162 418), lower := (rows 289 7 69 25 88 32 64 128 256), losses := [] }

theorem u5416 : Upper (D 3) (R 3) [288,5,65,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5416
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5417 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 25 146 232 232 232 488), lower := (rows 289 7 69 25 146 32 64 128 256), losses := [] }

theorem u5417 : Upper (D 3) (R 3) [288,5,65,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5417
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5418 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 25 152 226 226 226 482), lower := (rows 289 7 69 25 152 32 64 128 256), losses := [] }

theorem u5418 : Upper (D 3) (R 3) [288,5,65,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5418
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5419 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 25 208 170 234 170 426), lower := (rows 289 7 69 25 208 32 64 128 256), losses := [] }

theorem u5419 : Upper (D 3) (R 3) [288,5,65,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5419
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5420 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 81 168 232 168 424), lower := (rows 289 7 69 26 81 32 64 128 256), losses := [] }

theorem u5420 : Upper (D 3) (R 3) [288,5,65,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5421 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 88 161 225 161 417), lower := (rows 289 7 69 26 88 32 64 128 256), losses := [] }

theorem u5421 : Upper (D 3) (R 3) [288,5,65,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5421
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5422 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 112 169 201 137 393), lower := (rows 289 7 69 26 112 32 64 128 256), losses := [] }

theorem u5422 : Upper (D 3) (R 3) [288,5,65,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5422
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5423 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 145 232 232 232 488), lower := (rows 289 7 69 26 145 32 64 128 256), losses := [] }

theorem u5423 : Upper (D 3) (R 3) [288,5,65,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5423
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5424 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 152 225 225 225 481), lower := (rows 289 7 69 26 152 32 64 128 256), losses := [] }

theorem u5424 : Upper (D 3) (R 3) [288,5,65,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5424
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5425 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 176 233 201 201 457), lower := (rows 289 7 69 26 176 32 64 128 256), losses := [] }

theorem u5425 : Upper (D 3) (R 3) [288,5,65,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5425
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5426 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 208 169 233 169 425), lower := (rows 289 7 69 26 208 32 64 128 256), losses := [] }

theorem u5426 : Upper (D 3) (R 3) [288,5,65,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5426
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5427 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 81 184 216 152 408), lower := (rows 289 7 69 42 81 32 64 128 256), losses := [] }

theorem u5427 : Upper (D 3) (R 3) [288,5,65,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5427
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5428 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 88 177 209 145 401), lower := (rows 289 7 69 42 88 32 64 128 256), losses := [] }

theorem u5428 : Upper (D 3) (R 3) [288,5,65,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5428
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5429 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 145 248 216 216 472), lower := (rows 289 7 69 42 145 32 64 128 256), losses := [] }

theorem u5429 : Upper (D 3) (R 3) [288,5,65,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5429
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5430 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 152 241 209 209 465), lower := (rows 289 7 69 42 152 32 64 128 256), losses := [] }

theorem u5430 : Upper (D 3) (R 3) [288,5,65,34,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5430
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5431 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 208 185 217 153 409), lower := (rows 289 7 69 42 208 32 64 128 256), losses := [] }

theorem u5431 : Upper (D 3) (R 3) [288,5,65,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5431
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5432 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 81 170 202 138 394), lower := (rows 289 7 69 56 81 32 64 128 256), losses := [] }

theorem u5432 : Upper (D 3) (R 3) [288,5,65,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5432
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5433 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 82 169 201 137 393), lower := (rows 289 7 69 56 82 32 64 128 256), losses := [] }

theorem u5433 : Upper (D 3) (R 3) [288,5,65,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5433
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5434 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 145 234 202 202 458), lower := (rows 289 7 69 56 145 32 64 128 256), losses := [] }

theorem u5434 : Upper (D 3) (R 3) [288,5,65,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5434
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5435 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 146 233 201 201 457), lower := (rows 289 7 69 56 146 32 64 128 256), losses := [] }

theorem u5435 : Upper (D 3) (R 3) [288,5,65,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5435
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5436 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 56 208 171 203 139 395), lower := (rows 289 7 69 56 208 32 64 128 256), losses := [] }

theorem u5436 : Upper (D 3) (R 3) [288,5,65,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5436
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5437 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 73 146 184 248 184 440), lower := (rows 289 7 69 73 146 32 64 128 256), losses := [] }

theorem u5437 : Upper (D 3) (R 3) [288,5,65,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5437
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5438 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 73 152 178 242 178 434), lower := (rows 289 7 69 73 152 32 64 128 256), losses := [] }

theorem u5438 : Upper (D 3) (R 3) [288,5,65,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5438
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5439 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 73 176 186 218 154 410), lower := (rows 289 7 69 73 176 32 64 128 256), losses := [] }

theorem u5439 : Upper (D 3) (R 3) [288,5,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5439
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5440 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 145 184 248 184 440), lower := (rows 289 7 69 74 145 32 64 128 256), losses := [] }

theorem u5440 : Upper (D 3) (R 3) [288,5,65,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5440
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5441 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 152 177 241 177 433), lower := (rows 289 7 69 74 152 32 64 128 256), losses := [] }

theorem u5441 : Upper (D 3) (R 3) [288,5,65,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5442 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 176 185 217 153 409), lower := (rows 289 7 69 74 176 32 64 128 256), losses := [] }

theorem u5442 : Upper (D 3) (R 3) [288,5,65,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5443 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 88 145 170 234 170 426), lower := (rows 289 7 69 88 145 32 64 128 256), losses := [] }

theorem u5443 : Upper (D 3) (R 3) [288,5,65,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5443
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5444 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 88 146 169 233 169 425), lower := (rows 289 7 69 88 146 32 64 128 256), losses := [] }

theorem u5444 : Upper (D 3) (R 3) [288,5,65,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5444
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5445 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 88 152 163 227 163 419), lower := (rows 289 7 69 88 152 32 64 128 256), losses := [] }

theorem u5445 : Upper (D 3) (R 3) [288,5,65,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5446 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 88 176 171 203 139 395), lower := (rows 289 7 69 88 176 32 64 128 256), losses := [] }

theorem u5446 : Upper (D 3) (R 3) [288,5,65,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5446
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5447 : PairBound 9 := { available := 154, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 145 186 218 154 410), lower := (rows 289 7 69 104 145 32 64 128 256), losses := [] }

theorem u5447 : Upper (D 3) (R 3) [288,5,65,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5447
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5448 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 146 185 217 153 409), lower := (rows 289 7 69 104 146 32 64 128 256), losses := [] }

theorem u5448 : Upper (D 3) (R 3) [288,5,65,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5448
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5449 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 152 179 211 147 403), lower := (rows 289 7 69 104 152 32 64 128 256), losses := [] }

theorem u5449 : Upper (D 3) (R 3) [288,5,65,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5449
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5450 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 137 146 120 120 248 376), lower := (rows 289 7 69 137 146 32 64 128 256), losses := [] }

theorem u5450 : Upper (D 3) (R 3) [288,5,65,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5450
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5451 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 137 176 122 90 218 346), lower := (rows 289 7 69 137 176 32 64 128 256), losses := [] }

theorem u5451 : Upper (D 3) (R 3) [288,5,65,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5451
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5452 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 137 208 58 122 186 314), lower := (rows 289 7 69 137 208 32 64 128 256), losses := [] }

theorem u5452 : Upper (D 3) (R 3) [288,5,65,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5452
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5453 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 138 176 121 89 217 345), lower := (rows 289 7 69 138 176 32 64 128 256), losses := [] }

theorem u5453 : Upper (D 3) (R 3) [288,5,65,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5453
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5454 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 138 208 57 121 185 313), lower := (rows 289 7 69 138 208 32 64 128 256), losses := [] }

theorem u5454 : Upper (D 3) (R 3) [288,5,65,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5454
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5455 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 168 208 59 91 155 283), lower := (rows 289 7 69 168 208 32 64 128 256), losses := [] }

theorem u5455 : Upper (D 3) (R 3) [288,5,65,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5455
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5456 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 25 88 161 225 161 417), lower := (rows 289 7 70 25 88 32 64 128 256), losses := [] }

theorem u5456 : Upper (D 3) (R 3) [288,5,66,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5457 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 25 112 169 201 137 393), lower := (rows 289 7 70 25 112 32 64 128 256), losses := [] }

theorem u5457 : Upper (D 3) (R 3) [288,5,66,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5457
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5458_128 : Upper (D 3) (R 3) [288,5,66,17,136,128] 13 :=
  permutation_upper _ _ _ [288,5,66,17,136,64] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2089

def r5458 : Route 9 := (fun mask => (mask,id))

def c5458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5458 : Upper (D 3) (R 3) [288,5,66,17,136] 13 := by
  apply FastRouting.sound _ _ [288,5,66,17,136] 13 (by decide) (choices 1) [1,64,128] r5458 c5458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2088
  · exact u2089
  · exact m5458_128

def b5459 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 25 176 233 201 201 457), lower := (rows 289 7 70 25 176 32 64 128 256), losses := [] }

theorem u5459 : Upper (D 3) (R 3) [288,5,66,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5459
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5459
end Delivery.IrregularNine14.P03
