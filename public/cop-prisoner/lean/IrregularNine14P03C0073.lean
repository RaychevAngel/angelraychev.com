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

def b4380 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 176 353 321 449 321), lower := (rows 97 7 140 26 176 32 64 128 256), losses := [] }

theorem u4380 : Upper (D 3) (R 3) [96,5,136,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4380
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4381 : Route 9 := (fun mask => (mask,id))

def c4381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4381 : Upper (D 3) (R 3) [96,5,136,18,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,257] 13 (by decide) (choices 1) [1,64,128] r4381 c4381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1640
  · exact u1641
  · exact u1642

def b4382 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 97 7 140 26 304 225 193 193 449), lower := (rows 97 7 140 26 304 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 449 455 140 478 272 0 64 128 256) }] }

theorem u4382 : Upper (D 3) (R 3) [96,5,136,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4382
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4383 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 400 97 97 225 353), lower := (rows 97 7 140 26 400 32 64 128 256), losses := [] }

theorem u4383 : Upper (D 3) (R 3) [96,5,136,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4383
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4384 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 82 433 465 401 401), lower := (rows 97 7 140 41 82 32 64 128 256), losses := [] }

theorem u4384 : Upper (D 3) (R 3) [96,5,136,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4384
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4385 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 145 370 338 466 338), lower := (rows 97 7 140 41 145 32 64 128 256), losses := [] }

theorem u4385 : Upper (D 3) (R 3) [96,5,136,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4385
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4386 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 208 307 339 403 275), lower := (rows 97 7 140 41 208 32 64 128 256), losses := [] }

theorem u4386 : Upper (D 3) (R 3) [96,5,136,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4386
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4387 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 273 242 210 210 466), lower := (rows 97 7 140 41 273 32 64 128 256), losses := [] }

theorem u4387 : Upper (D 3) (R 3) [96,5,136,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4387
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4388 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 274 241 209 209 465), lower := (rows 97 7 140 41 274 32 64 128 256), losses := [] }

theorem u4388 : Upper (D 3) (R 3) [96,5,136,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4388
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4389 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 336 179 211 147 403), lower := (rows 97 7 140 41 336 32 64 128 256), losses := [] }

theorem u4389 : Upper (D 3) (R 3) [96,5,136,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4389
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4390 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 400 115 83 211 339), lower := (rows 97 7 140 41 400 32 64 128 256), losses := [] }

theorem u4390 : Upper (D 3) (R 3) [96,5,136,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4390
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4391 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 42 145 369 337 465 337), lower := (rows 97 7 140 42 145 32 64 128 256), losses := [] }

theorem u4391 : Upper (D 3) (R 3) [96,5,136,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4391
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4392 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 42 208 305 337 401 273), lower := (rows 97 7 140 42 208 32 64 128 256), losses := [] }

theorem u4392 : Upper (D 3) (R 3) [96,5,136,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4392
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4393 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 42 273 241 209 209 465), lower := (rows 97 7 140 42 273 32 64 128 256), losses := [] }

theorem u4393 : Upper (D 3) (R 3) [96,5,136,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4393
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4394 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 42 336 177 209 145 401), lower := (rows 97 7 140 42 336 32 64 128 256), losses := [] }

theorem u4394 : Upper (D 3) (R 3) [96,5,136,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4394
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4395 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 42 400 113 81 209 337), lower := (rows 97 7 140 42 400 32 64 128 256), losses := [] }

theorem u4395 : Upper (D 3) (R 3) [96,5,136,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4395
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4396 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 56 82 417 449 385 385), lower := (rows 97 7 140 56 82 32 64 128 256), losses := [] }

theorem u4396 : Upper (D 3) (R 3) [96,5,136,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4396
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4397 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 145 355 323 451 323), lower := (rows 97 7 140 56 145 32 64 128 256), losses := [] }

theorem u4397 : Upper (D 3) (R 3) [96,5,136,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4397
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4398 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 146 353 321 449 321), lower := (rows 97 7 140 56 146 32 64 128 256), losses := [] }

theorem u4398 : Upper (D 3) (R 3) [96,5,136,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4398
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4399 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 208 291 323 387 259), lower := (rows 97 7 140 56 208 32 64 128 256), losses := [] }

theorem u4399 : Upper (D 3) (R 3) [96,5,136,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4399
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4400 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 56 273 227 195 195 451), lower := (rows 97 7 140 56 273 32 64 128 256), losses := [] }

theorem u4400 : Upper (D 3) (R 3) [96,5,136,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4400
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4401 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 56 274 225 193 193 449), lower := (rows 97 7 140 56 274 32 64 128 256), losses := [] }

theorem u4401 : Upper (D 3) (R 3) [96,5,136,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4401
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4402 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 56 336 163 195 131 387), lower := (rows 97 7 140 56 336 32 64 128 256), losses := [] }

theorem u4402 : Upper (D 3) (R 3) [96,5,136,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4402
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4403 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 56 400 99 67 195 323), lower := (rows 97 7 140 56 400 32 64 128 256), losses := [] }

theorem u4403 : Upper (D 3) (R 3) [96,5,136,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4403
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4404 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 145 307 339 403 275), lower := (rows 97 7 140 104 145 32 64 128 256), losses := [] }

theorem u4404 : Upper (D 3) (R 3) [96,5,136,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4404
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4405 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 273 179 211 147 403), lower := (rows 97 7 140 104 273 32 64 128 256), losses := [] }

theorem u4405 : Upper (D 3) (R 3) [96,5,136,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4405
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4406 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 274 177 209 145 401), lower := (rows 97 7 140 104 274 32 64 128 256), losses := [] }

theorem u4406 : Upper (D 3) (R 3) [96,5,136,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4406
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4407 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 400 51 83 147 275), lower := (rows 97 7 140 104 400 32 64 128 256), losses := [] }

theorem u4407 : Upper (D 3) (R 3) [96,5,136,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4407
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4408 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 50 369 337 465 337), lower := (rows 97 7 140 137 50 32 64 128 256), losses := [] }

theorem u4408 : Upper (D 3) (R 3) [96,5,136,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4408
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4409 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 273 114 114 242 370), lower := (rows 97 7 140 137 273 32 64 128 256), losses := [] }

theorem u4409 : Upper (D 3) (R 3) [96,5,136,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4409
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4410 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 274 113 113 241 369), lower := (rows 97 7 140 137 274 32 64 128 256), losses := [] }

theorem u4410 : Upper (D 3) (R 3) [96,5,136,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4410
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4411 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 304 115 83 211 339), lower := (rows 97 7 140 137 304 32 64 128 256), losses := [] }

theorem u4411 : Upper (D 3) (R 3) [96,5,136,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4411
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4412 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 273 113 113 241 369), lower := (rows 97 7 140 138 273 32 64 128 256), losses := [] }

theorem u4412 : Upper (D 3) (R 3) [96,5,136,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4412
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4413 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 304 113 81 209 337), lower := (rows 97 7 140 138 304 32 64 128 256), losses := [] }

theorem u4413 : Upper (D 3) (R 3) [96,5,136,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4413
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4414 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 50 353 321 449 321), lower := (rows 97 7 140 152 50 32 64 128 256), losses := [] }

theorem u4414 : Upper (D 3) (R 3) [96,5,136,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4414
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4415 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 273 99 99 227 355), lower := (rows 97 7 140 152 273 32 64 128 256), losses := [] }

theorem u4415 : Upper (D 3) (R 3) [96,5,136,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4415
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4416 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 274 97 97 225 353), lower := (rows 97 7 140 152 274 32 64 128 256), losses := [] }

theorem u4416 : Upper (D 3) (R 3) [96,5,136,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4416
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4417 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 304 99 67 195 323), lower := (rows 97 7 140 152 304 32 64 128 256), losses := [] }

theorem u4417 : Upper (D 3) (R 3) [96,5,136,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4417
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4418 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 82 305 337 401 273), lower := (rows 97 7 140 168 82 32 64 128 256), losses := [] }

theorem u4418 : Upper (D 3) (R 3) [96,5,136,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4418
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4419 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 273 115 83 211 339), lower := (rows 97 7 140 168 273 32 64 128 256), losses := [] }

theorem u4419 : Upper (D 3) (R 3) [96,5,136,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4419
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4420 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 274 113 81 209 337), lower := (rows 97 7 140 168 274 32 64 128 256), losses := [] }

theorem u4420 : Upper (D 3) (R 3) [96,5,136,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4421 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 336 51 83 147 275), lower := (rows 97 7 140 168 336 32 64 128 256), losses := [] }

theorem u4421 : Upper (D 3) (R 3) [96,5,136,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4421
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4422 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 265 49 242 210 210 466), lower := (rows 97 7 140 265 49 32 64 128 256), losses := [] }

theorem u4422 : Upper (D 3) (R 3) [96,5,136,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4422
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4423 : Route 9 := (fun mask => (mask,id))

def c4423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4423 : Upper (D 3) (R 3) [96,5,136,257,34] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,34] 13 (by decide) (choices 1) [1,16,64,128] r4423 c4423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1643
  · exact u1644
  · exact u1645
  · exact u1646

def b4424 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 265 112 179 211 147 403), lower := (rows 97 7 140 265 112 32 64 128 256), losses := [] }

theorem u4424 : Upper (D 3) (R 3) [96,5,136,257,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4424
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4425 : Route 9 := (fun mask => (mask,id))

def c4425 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4425 : Upper (D 3) (R 3) [96,5,136,257,129] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,129] 13 (by decide) (choices 1) [2,16,64] r4425 c4425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1647
  · exact u1648
  · exact u1649

def b4426 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 265 146 113 113 241 369), lower := (rows 97 7 140 265 146 32 64 128 256), losses := [] }

theorem u4426 : Upper (D 3) (R 3) [96,5,136,257,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4426
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4427 : Route 9 := (fun mask => (mask,id))

def c4427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4427 : Upper (D 3) (R 3) [96,5,136,257,160] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,160] 13 (by decide) (choices 1) [1,2,16,64] r4427 c4427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1650
  · exact u1651
  · exact u1652
  · exact u1653

def b4428 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 266 49 241 209 209 465), lower := (rows 97 7 140 266 49 32 64 128 256), losses := [] }

theorem u4428 : Upper (D 3) (R 3) [96,5,136,258,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4428
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4429 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 266 112 177 209 145 401), lower := (rows 97 7 140 266 112 32 64 128 256), losses := [] }

theorem u4429 : Upper (D 3) (R 3) [96,5,136,258,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4429
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4430 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 266 145 113 113 241 369), lower := (rows 97 7 140 266 145 32 64 128 256), losses := [] }

theorem u4430 : Upper (D 3) (R 3) [96,5,136,258,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4430
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4431 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 266 176 113 81 209 337), lower := (rows 97 7 140 266 176 32 64 128 256), losses := [] }

theorem u4431 : Upper (D 3) (R 3) [96,5,136,258,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4431
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4432 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 280 49 227 195 195 451), lower := (rows 97 7 140 280 49 32 64 128 256), losses := [] }

theorem u4432 : Upper (D 3) (R 3) [96,5,136,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4432
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4433 : PairBound 9 := { available := 193, camps := [], pairs := [(2,5)], upper := (rows 97 7 140 280 50 225 193 193 449), lower := (rows 97 7 140 280 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 67 131 259), good := (rows 449 455 140 284 478 0 64 128 256) }] }

theorem u4433 : Upper (D 3) (R 3) [96,5,136,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4433
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4434 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 280 112 163 195 131 387), lower := (rows 97 7 140 280 112 32 64 128 256), losses := [] }

theorem u4434 : Upper (D 3) (R 3) [96,5,136,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4434
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4435 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 145 99 99 227 355), lower := (rows 97 7 140 280 145 32 64 128 256), losses := [] }

theorem u4435 : Upper (D 3) (R 3) [96,5,136,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4435
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4436 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 146 97 97 225 353), lower := (rows 97 7 140 280 146 32 64 128 256), losses := [] }

theorem u4436 : Upper (D 3) (R 3) [96,5,136,272,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4436
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4437 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 280 176 99 67 195 323), lower := (rows 97 7 140 280 176 32 64 128 256), losses := [] }

theorem u4437 : Upper (D 3) (R 3) [96,5,136,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4437
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4438 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 296 82 177 209 145 401), lower := (rows 97 7 140 296 82 32 64 128 256), losses := [] }

theorem u4438 : Upper (D 3) (R 3) [96,5,136,288,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4438
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4439 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 296 145 115 83 211 339), lower := (rows 97 7 140 296 145 32 64 128 256), losses := [] }

theorem u4439 : Upper (D 3) (R 3) [96,5,136,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4439
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4439
end Delivery.IrregularNine14.P03
