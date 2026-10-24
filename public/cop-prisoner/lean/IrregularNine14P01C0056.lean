import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 291, camps := [], pairs := [], upper := (rows 53 82 134 200 24 291 355 419 291), lower := (rows 53 82 134 200 24 32 64 128 256), losses := [] }

theorem u3360 : Upper (D 1) (R 1) [52,80,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 134 200 48 299 331 395 267), lower := (rows 53 82 134 200 48 32 64 128 256), losses := [] }

theorem u3361 : Upper (D 1) (R 1) [52,80,130,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3362 : PairBound 9 := { available := 43, camps := [], pairs := [], upper := (rows 53 82 134 200 272 43 107 171 299), lower := (rows 53 82 134 200 272 32 64 128 256), losses := [] }

theorem u3362 : Upper (D 1) (R 1) [52,80,130,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3363 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 265 18 232 232 232 488), lower := (rows 53 82 134 265 18 32 64 128 256), losses := [] }

theorem u3363 : Upper (D 1) (R 1) [52,80,130,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3364 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 82 134 265 24 226 226 226 482), lower := (rows 53 82 134 265 24 32 64 128 256), losses := [] }

theorem u3364 : Upper (D 1) (R 1) [52,80,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3365 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 134 265 48 234 202 202 458), lower := (rows 53 82 134 265 48 32 64 128 256), losses := [] }

theorem u3365 : Upper (D 1) (R 1) [52,80,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3366 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 134 265 80 170 234 170 426), lower := (rows 53 82 134 265 80 32 64 128 256), losses := [] }

theorem u3366 : Upper (D 1) (R 1) [52,80,130,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3367 : PairBound 9 := { available := 106, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 265 144 106 106 234 362), lower := (rows 53 82 134 265 144 32 64 128 256), losses := [] }

theorem u3367 : Upper (D 1) (R 1) [52,80,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 53 82 134 266 17 232 232 232 488), lower := (rows 53 82 134 266 17 32 64 128 256), losses := [] }

theorem u3368 : Upper (D 1) (R 1) [52,80,130,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 53 82 134 266 24 225 225 225 481), lower := (rows 53 82 134 266 24 32 64 128 256), losses := [] }

theorem u3369 : Upper (D 1) (R 1) [52,80,130,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 134 266 48 233 201 201 457), lower := (rows 53 82 134 266 48 32 64 128 256), losses := [] }

theorem u3370 : Upper (D 1) (R 1) [52,80,130,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 134 266 80 169 233 169 425), lower := (rows 53 82 134 266 80 32 64 128 256), losses := [] }

theorem u3371 : Upper (D 1) (R 1) [52,80,130,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 266 144 105 105 233 361), lower := (rows 53 82 134 266 144 32 64 128 256), losses := [] }

theorem u3372 : Upper (D 1) (R 1) [52,80,130,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 53 82 134 296 17 234 202 202 458), lower := (rows 53 82 134 296 17 32 64 128 256), losses := [] }

theorem u3373 : Upper (D 1) (R 1) [52,80,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 296 18 233 201 201 457), lower := (rows 53 82 134 296 18 32 64 128 256), losses := [] }

theorem u3374 : Upper (D 1) (R 1) [52,80,130,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 53 82 134 296 24 227 195 195 451), lower := (rows 53 82 134 296 24 32 64 128 256), losses := [] }

theorem u3375 : Upper (D 1) (R 1) [52,80,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 134 296 80 171 203 139 395), lower := (rows 53 82 134 296 80 32 64 128 256), losses := [] }

theorem u3376 : Upper (D 1) (R 1) [52,80,130,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 296 144 107 75 203 331), lower := (rows 53 82 134 296 144 32 64 128 256), losses := [] }

theorem u3377 : Upper (D 1) (R 1) [52,80,130,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 82 134 328 17 170 234 170 426), lower := (rows 53 82 134 328 17 32 64 128 256), losses := [] }

theorem u3378 : Upper (D 1) (R 1) [52,80,130,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 328 18 169 233 169 425), lower := (rows 53 82 134 328 18 32 64 128 256), losses := [] }

theorem u3379 : Upper (D 1) (R 1) [52,80,130,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3379
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 82 134 328 24 163 227 163 419), lower := (rows 53 82 134 328 24 32 64 128 256), losses := [] }

theorem u3380 : Upper (D 1) (R 1) [52,80,130,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 134 328 48 171 203 139 395), lower := (rows 53 82 134 328 48 32 64 128 256), losses := [] }

theorem u3381 : Upper (D 1) (R 1) [52,80,130,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3382 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 134 328 144 43 107 171 299), lower := (rows 53 82 134 328 144 32 64 128 256), losses := [] }

theorem u3382 : Upper (D 1) (R 1) [52,80,130,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3383 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 53 82 134 392 17 106 106 234 362), lower := (rows 53 82 134 392 17 32 64 128 256), losses := [] }

theorem u3383 : Upper (D 1) (R 1) [52,80,130,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3384 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 82 134 392 18 105 105 233 361), lower := (rows 53 82 134 392 18 32 64 128 256), losses := [] }

theorem u3384 : Upper (D 1) (R 1) [52,80,130,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3385 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 53 82 134 392 24 99 99 227 355), lower := (rows 53 82 134 392 24 32 64 128 256), losses := [] }

theorem u3385 : Upper (D 1) (R 1) [52,80,130,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3386 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 134 392 48 107 75 203 331), lower := (rows 53 82 134 392 48 32 64 128 256), losses := [] }

theorem u3386 : Upper (D 1) (R 1) [52,80,130,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3386
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3387 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 134 392 80 43 107 171 299), lower := (rows 53 82 134 392 80 32 64 128 256), losses := [] }

theorem u3387 : Upper (D 1) (R 1) [52,80,130,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3387
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 73 18 418 482 418 418), lower := (rows 53 82 140 73 18 32 64 128 256), losses := [] }

theorem u3388 : Upper (D 1) (R 1) [52,80,136,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3389 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 73 48 418 450 386 386), lower := (rows 53 82 140 73 48 32 64 128 256), losses := [] }

theorem u3389 : Upper (D 1) (R 1) [52,80,136,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3390 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 140 73 144 290 354 418 290), lower := (rows 53 82 140 73 144 32 64 128 256), losses := [] }

theorem u3390 : Upper (D 1) (R 1) [52,80,136,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 140 73 272 162 226 162 418), lower := (rows 53 82 140 73 272 32 64 128 256), losses := [] }

theorem u3391 : Upper (D 1) (R 1) [52,80,136,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3391
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 226, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 265 18 226 226 226 482), lower := (rows 53 82 140 265 18 32 64 128 256), losses := [] }

theorem u3392 : Upper (D 1) (R 1) [52,80,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3393 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 265 48 226 194 194 450), lower := (rows 53 82 140 265 48 32 64 128 256), losses := [] }

theorem u3393 : Upper (D 1) (R 1) [52,80,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3393
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 140 265 80 162 226 162 418), lower := (rows 53 82 140 265 80 32 64 128 256), losses := [] }

theorem u3394 : Upper (D 1) (R 1) [52,80,136,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 140 265 144 98 98 226 354), lower := (rows 53 82 140 265 144 32 64 128 256), losses := [] }

theorem u3395 : Upper (D 1) (R 1) [52,80,136,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3396 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 82 140 266 17 226 226 226 482), lower := (rows 53 82 140 266 17 32 64 128 256), losses := [] }

theorem u3396 : Upper (D 1) (R 1) [52,80,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3396
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3397 : PairBound 9 := { available := 225, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 266 18 225 225 225 481), lower := (rows 53 82 140 266 18 32 64 128 256), losses := [] }

theorem u3397 : Upper (D 1) (R 1) [52,80,136,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3398 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 266 48 227 195 195 451), lower := (rows 53 82 140 266 48 32 64 128 256), losses := [] }

theorem u3398 : Upper (D 1) (R 1) [52,80,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 53 82 140 266 80 163 227 163 419), lower := (rows 53 82 140 266 80 32 64 128 256), losses := [] }

theorem u3399 : Upper (D 1) (R 1) [52,80,136,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3399
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 140 266 144 99 99 227 355), lower := (rows 53 82 140 266 144 32 64 128 256), losses := [] }

theorem u3400 : Upper (D 1) (R 1) [52,80,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 82 140 328 17 162 226 162 418), lower := (rows 53 82 140 328 17 32 64 128 256), losses := [] }

theorem u3401 : Upper (D 1) (R 1) [52,80,136,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3402 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 328 18 163 227 163 419), lower := (rows 53 82 140 328 18 32 64 128 256), losses := [] }

theorem u3402 : Upper (D 1) (R 1) [52,80,136,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 140 328 48 163 195 131 387), lower := (rows 53 82 140 328 48 32 64 128 256), losses := [] }

theorem u3403 : Upper (D 1) (R 1) [52,80,136,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 140 328 144 35 99 163 291), lower := (rows 53 82 140 328 144 32 64 128 256), losses := [] }

theorem u3404 : Upper (D 1) (R 1) [52,80,136,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 394, camps := [], pairs := [], upper := (rows 53 82 196 42 17 426 458 394 394), lower := (rows 53 82 196 42 17 32 64 128 256), losses := [] }

theorem u3405 : Upper (D 1) (R 1) [52,80,192,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 42 18 425 457 393 393), lower := (rows 53 82 196 42 18 32 64 128 256), losses := [] }

theorem u3406 : Upper (D 1) (R 1) [52,80,192,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3407 : PairBound 9 := { available := 387, camps := [], pairs := [], upper := (rows 53 82 196 42 24 419 451 387 387), lower := (rows 53 82 196 42 24 32 64 128 256), losses := [] }

theorem u3407 : Upper (D 1) (R 1) [52,80,192,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3408 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 82 196 42 144 299 331 395 267), lower := (rows 53 82 196 42 144 32 64 128 256), losses := [] }

theorem u3408 : Upper (D 1) (R 1) [52,80,192,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3409 : PairBound 9 := { available := 139, camps := [], pairs := [], upper := (rows 53 82 196 42 272 171 203 139 395), lower := (rows 53 82 196 42 272 32 64 128 256), losses := [] }

theorem u3409 : Upper (D 1) (R 1) [52,80,192,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3409
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3410 : PairBound 9 := { available := 298, camps := [], pairs := [], upper := (rows 53 82 196 138 17 298 362 426 298), lower := (rows 53 82 196 138 17 32 64 128 256), losses := [] }

theorem u3410 : Upper (D 1) (R 1) [52,80,192,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3410
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3411 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 138 18 297 361 425 297), lower := (rows 53 82 196 138 18 32 64 128 256), losses := [] }

theorem u3411 : Upper (D 1) (R 1) [52,80,192,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3412 : PairBound 9 := { available := 291, camps := [], pairs := [], upper := (rows 53 82 196 138 24 291 355 419 291), lower := (rows 53 82 196 138 24 32 64 128 256), losses := [] }

theorem u3412 : Upper (D 1) (R 1) [52,80,192,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3412
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3413 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 138 48 299 331 395 267), lower := (rows 53 82 196 138 48 32 64 128 256), losses := [] }

theorem u3413 : Upper (D 1) (R 1) [52,80,192,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3414 : PairBound 9 := { available := 43, camps := [], pairs := [], upper := (rows 53 82 196 138 272 43 107 171 299), lower := (rows 53 82 196 138 272 32 64 128 256), losses := [] }

theorem u3414 : Upper (D 1) (R 1) [52,80,192,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3414
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3415 : PairBound 9 := { available := 266, camps := [], pairs := [], upper := (rows 53 82 196 168 17 298 330 394 266), lower := (rows 53 82 196 168 17 32 64 128 256), losses := [] }

theorem u3415 : Upper (D 1) (R 1) [52,80,192,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3415
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3416 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 168 18 299 331 395 267), lower := (rows 53 82 196 168 18 32 64 128 256), losses := [] }

theorem u3416 : Upper (D 1) (R 1) [52,80,192,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3417 : PairBound 9 := { available := 259, camps := [], pairs := [], upper := (rows 53 82 196 168 24 291 323 387 259), lower := (rows 53 82 196 168 24 32 64 128 256), losses := [] }

theorem u3417 : Upper (D 1) (R 1) [52,80,192,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3418 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 53 82 196 168 272 43 75 139 267), lower := (rows 53 82 196 168 272 32 64 128 256), losses := [] }

theorem u3418 : Upper (D 1) (R 1) [52,80,192,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3419 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 82 196 265 18 170 234 170 426), lower := (rows 53 82 196 265 18 32 64 128 256), losses := [] }

theorem u3419 : Upper (D 1) (R 1) [52,80,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3419
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3419
end Delivery.IrregularNine14.P01
