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

def b4320 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 400 121 89 217 345), lower := (rows 97 7 133 42 400 32 64 128 256), losses := [] }

theorem u4320 : Upper (D 3) (R 3) [96,5,129,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4320
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4321 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 145 362 330 458 330), lower := (rows 97 7 133 56 145 32 64 128 256), losses := [] }

theorem u4321 : Upper (D 3) (R 3) [96,5,129,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4322 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 146 361 329 457 329), lower := (rows 97 7 133 56 146 32 64 128 256), losses := [] }

theorem u4322 : Upper (D 3) (R 3) [96,5,129,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4323 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 208 299 331 395 267), lower := (rows 97 7 133 56 208 32 64 128 256), losses := [] }

theorem u4323 : Upper (D 3) (R 3) [96,5,129,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4323
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4324 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 273 234 202 202 458), lower := (rows 97 7 133 56 273 32 64 128 256), losses := [] }

theorem u4324 : Upper (D 3) (R 3) [96,5,129,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4324
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4325 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 274 233 201 201 457), lower := (rows 97 7 133 56 274 32 64 128 256), losses := [] }

theorem u4325 : Upper (D 3) (R 3) [96,5,129,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4325
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4326 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 336 171 203 139 395), lower := (rows 97 7 133 56 336 32 64 128 256), losses := [] }

theorem u4326 : Upper (D 3) (R 3) [96,5,129,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4326
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4327 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 56 400 107 75 203 331), lower := (rows 97 7 133 56 400 32 64 128 256), losses := [] }

theorem u4327 : Upper (D 3) (R 3) [96,5,129,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4327
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4328 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 137 274 120 120 248 376), lower := (rows 97 7 133 137 274 32 64 128 256), losses := [] }

theorem u4328 : Upper (D 3) (R 3) [96,5,129,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4328
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4329 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 137 280 114 114 242 370), lower := (rows 97 7 133 137 280 32 64 128 256), losses := [] }

theorem u4329 : Upper (D 3) (R 3) [96,5,129,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4329
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4330 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 137 304 122 90 218 346), lower := (rows 97 7 133 137 304 32 64 128 256), losses := [] }

theorem u4330 : Upper (D 3) (R 3) [96,5,129,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4330
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4331 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 273 120 120 248 376), lower := (rows 97 7 133 138 273 32 64 128 256), losses := [] }

theorem u4331 : Upper (D 3) (R 3) [96,5,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4331
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4332 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 280 113 113 241 369), lower := (rows 97 7 133 138 280 32 64 128 256), losses := [] }

theorem u4332 : Upper (D 3) (R 3) [96,5,129,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4332
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4333 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 304 121 89 217 345), lower := (rows 97 7 133 138 304 32 64 128 256), losses := [] }

theorem u4333 : Upper (D 3) (R 3) [96,5,129,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4333
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4334 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 273 106 106 234 362), lower := (rows 97 7 133 152 273 32 64 128 256), losses := [] }

theorem u4334 : Upper (D 3) (R 3) [96,5,129,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4334
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4335 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 274 105 105 233 361), lower := (rows 97 7 133 152 274 32 64 128 256), losses := [] }

theorem u4335 : Upper (D 3) (R 3) [96,5,129,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4335
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4336 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 280 99 99 227 355), lower := (rows 97 7 133 152 280 32 64 128 256), losses := [] }

theorem u4336 : Upper (D 3) (R 3) [96,5,129,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4336
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4337 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 152 304 107 75 203 331), lower := (rows 97 7 133 152 304 32 64 128 256), losses := [] }

theorem u4337 : Upper (D 3) (R 3) [96,5,129,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4337
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4338 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 273 122 90 218 346), lower := (rows 97 7 133 168 273 32 64 128 256), losses := [] }

theorem u4338 : Upper (D 3) (R 3) [96,5,129,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4338
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4339 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 274 121 89 217 345), lower := (rows 97 7 133 168 274 32 64 128 256), losses := [] }

theorem u4339 : Upper (D 3) (R 3) [96,5,129,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4339
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4340 : PairBound 9 := { available := 83, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 280 115 83 211 339), lower := (rows 97 7 133 168 280 32 64 128 256), losses := [] }

theorem u4340 : Upper (D 3) (R 3) [96,5,129,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4340
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4341 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 336 59 91 155 283), lower := (rows 97 7 133 168 336 32 64 128 256), losses := [] }

theorem u4341 : Upper (D 3) (R 3) [96,5,129,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4341
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4342 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 25 152 353 353 481 353), lower := (rows 97 7 134 25 152 32 64 128 256), losses := [] }

theorem u4342 : Upper (D 3) (R 3) [96,5,130,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4342
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4343 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 25 176 361 329 457 329), lower := (rows 97 7 134 25 176 32 64 128 256), losses := [] }

theorem u4343 : Upper (D 3) (R 3) [96,5,130,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4343
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4344 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 134 25 273 232 232 232 488), lower := (rows 97 7 134 25 273 32 64 128 256), losses := [] }

theorem u4344 : Upper (D 3) (R 3) [96,5,130,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4344
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4345 : Route 9 := (fun mask => (mask,id))

def c4345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4345 : Upper (D 3) (R 3) [96,5,130,17,264] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17,264] 13 (by decide) (choices 1) [1,64,128] r4345 c4345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1627
  · exact u1628
  · exact u1629

def b4346 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 25 304 233 201 201 457), lower := (rows 97 7 134 25 304 32 64 128 256), losses := [] }

theorem u4346 : Upper (D 3) (R 3) [96,5,130,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4347 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 25 400 105 105 233 361), lower := (rows 97 7 134 25 400 32 64 128 256), losses := [] }

theorem u4347 : Upper (D 3) (R 3) [96,5,130,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4347
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4348 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 41 88 433 465 401 401), lower := (rows 97 7 134 41 88 32 64 128 256), losses := [] }

theorem u4348 : Upper (D 3) (R 3) [96,5,130,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4348
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4349 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 41 273 248 216 216 472), lower := (rows 97 7 134 41 273 32 64 128 256), losses := [] }

theorem u4349 : Upper (D 3) (R 3) [96,5,130,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4349
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4350 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 41 280 241 209 209 465), lower := (rows 97 7 134 41 280 32 64 128 256), losses := [] }

theorem u4350 : Upper (D 3) (R 3) [96,5,130,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4350
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4351 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 41 336 185 217 153 409), lower := (rows 97 7 134 41 336 32 64 128 256), losses := [] }

theorem u4351 : Upper (D 3) (R 3) [96,5,130,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4351
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4352 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 56 88 417 449 385 385), lower := (rows 97 7 134 56 88 32 64 128 256), losses := [] }

theorem u4352 : Upper (D 3) (R 3) [96,5,130,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4352
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4353 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 56 145 361 329 457 329), lower := (rows 97 7 134 56 145 32 64 128 256), losses := [] }

theorem u4353 : Upper (D 3) (R 3) [96,5,130,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4353
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4354 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 56 152 353 321 449 321), lower := (rows 97 7 134 56 152 32 64 128 256), losses := [] }

theorem u4354 : Upper (D 3) (R 3) [96,5,130,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4354
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4355 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 297, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 208 297 329 393 265), lower := (rows 97 7 134 56 208 32 64 128 256), losses := [] }

theorem u4355 : Upper (D 3) (R 3) [96,5,130,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4355
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4356 : Route 9 := (fun mask => (mask,id))

def c4356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4356 : Upper (D 3) (R 3) [96,5,130,48,257] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,257] 13 (by decide) (choices 1) [1,8,64,128] r4356 c4356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1630
  · exact u1631
  · exact u1632
  · exact u1633

def b4357 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 56 280 225 193 193 449), lower := (rows 97 7 134 56 280 32 64 128 256), losses := [] }

theorem u4357 : Upper (D 3) (R 3) [96,5,130,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4358 : Route 9 := (fun mask => (mask,id))

def c4358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4358 : Upper (D 3) (R 3) [96,5,130,48,320] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48,320] 13 (by decide) (choices 1) [1,8,128] r4358 c4358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1634
  · exact u1635
  · exact u1636

def b4359 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 400 105 73 201 329), lower := (rows 97 7 134 56 400 32 64 128 256), losses := [] }

theorem u4359 : Upper (D 3) (R 3) [96,5,130,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4359
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4360 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 104 273 185 217 153 409), lower := (rows 97 7 134 104 273 32 64 128 256), losses := [] }

theorem u4360 : Upper (D 3) (R 3) [96,5,130,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4360
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4361 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 104 280 177 209 145 401), lower := (rows 97 7 134 104 280 32 64 128 256), losses := [] }

theorem u4361 : Upper (D 3) (R 3) [96,5,130,96,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4361
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4362 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 273 120 120 248 376), lower := (rows 97 7 134 137 273 32 64 128 256), losses := [] }

theorem u4362 : Upper (D 3) (R 3) [96,5,130,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4362
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4363 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 280 113 113 241 369), lower := (rows 97 7 134 137 280 32 64 128 256), losses := [] }

theorem u4363 : Upper (D 3) (R 3) [96,5,130,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4363
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4364 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 304 121 89 217 345), lower := (rows 97 7 134 137 304 32 64 128 256), losses := [] }

theorem u4364 : Upper (D 3) (R 3) [96,5,130,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4365 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 273 105 105 233 361), lower := (rows 97 7 134 152 273 32 64 128 256), losses := [] }

theorem u4365 : Upper (D 3) (R 3) [96,5,130,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4366 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 280 97 97 225 353), lower := (rows 97 7 134 152 280 32 64 128 256), losses := [] }

theorem u4366 : Upper (D 3) (R 3) [96,5,130,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4366
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4367 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 304 105 73 201 329), lower := (rows 97 7 134 152 304 32 64 128 256), losses := [] }

theorem u4367 : Upper (D 3) (R 3) [96,5,130,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4368 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 273 121 89 217 345), lower := (rows 97 7 134 168 273 32 64 128 256), losses := [] }

theorem u4368 : Upper (D 3) (R 3) [96,5,130,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4369 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 280 113 81 209 337), lower := (rows 97 7 134 168 280 32 64 128 256), losses := [] }

theorem u4369 : Upper (D 3) (R 3) [96,5,130,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4369
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4370 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 336 57 89 153 281), lower := (rows 97 7 134 168 336 32 64 128 256), losses := [] }

theorem u4370 : Upper (D 3) (R 3) [96,5,130,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4370
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4371 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 146 353 353 481 353), lower := (rows 97 7 140 25 146 32 64 128 256), losses := [] }

theorem u4371 : Upper (D 3) (R 3) [96,5,136,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4371
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4372 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 176 355 323 451 323), lower := (rows 97 7 140 25 176 32 64 128 256), losses := [] }

theorem u4372 : Upper (D 3) (R 3) [96,5,136,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4372
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4373 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 140 25 273 226 226 226 482), lower := (rows 97 7 140 25 273 32 64 128 256), losses := [] }

theorem u4373 : Upper (D 3) (R 3) [96,5,136,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4373
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r4374 : Route 9 := (fun mask => (mask,id))

def c4374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4374 : Upper (D 3) (R 3) [96,5,136,17,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17,258] 13 (by decide) (choices 1) [1,64,128] r4374 c4374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1637
  · exact u1638
  · exact u1639

def b4375 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 25 304 227 195 195 451), lower := (rows 97 7 140 25 304 32 64 128 256), losses := [] }

theorem u4375 : Upper (D 3) (R 3) [96,5,136,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4375
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4376 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 400 99 99 227 355), lower := (rows 97 7 140 25 400 32 64 128 256), losses := [] }

theorem u4376 : Upper (D 3) (R 3) [96,5,136,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4376
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4377 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 26 49 481 449 449 449), lower := (rows 97 7 140 26 49 32 64 128 256), losses := [] }

theorem u4377 : Upper (D 3) (R 3) [96,5,136,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4377
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4378 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 140 26 112 417 449 385 385), lower := (rows 97 7 140 26 112 32 64 128 256), losses := [] }

theorem u4378 : Upper (D 3) (R 3) [96,5,136,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4378
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b4379 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 26 145 353 353 481 353), lower := (rows 97 7 140 26 145 32 64 128 256), losses := [] }

theorem u4379 : Upper (D 3) (R 3) [96,5,136,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b4379
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u4379
end Delivery.IrregularNine14.P03
