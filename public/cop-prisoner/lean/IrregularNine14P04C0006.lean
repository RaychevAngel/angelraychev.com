import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0001

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 88 400 57 89 153 281), lower := (rows 7 14 38 88 400 32 64 128 256), losses := [] }

theorem u360 : Upper (D 4) (R 4) [6,12,34,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b360
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 200 25 305 337 401 273), lower := (rows 7 14 38 200 25 32 64 128 256), losses := [] }

theorem u361 : Upper (D 4) (R 4) [6,12,34,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b361
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 200 273 57 89 153 281), lower := (rows 7 14 38 200 273 32 64 128 256), losses := [] }

theorem u362 : Upper (D 4) (R 4) [6,12,34,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b362
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 14 38 200 280 49 81 145 273), lower := (rows 7 14 38 200 280 32 64 128 256), losses := [] }

theorem u363 : Upper (D 4) (R 4) [6,12,34,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b363
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 25 208 307 339 403 275), lower := (rows 7 14 44 25 208 32 64 128 256), losses := [] }

theorem u364 : Upper (D 4) (R 4) [6,12,40,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b364
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 73 400 51 83 147 275), lower := (rows 7 14 44 73 400 32 64 128 256), losses := [] }

theorem u365 : Upper (D 4) (R 4) [6,12,40,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b365
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 88 145 307 339 403 275), lower := (rows 7 14 44 88 145 32 64 128 256), losses := [] }

theorem u366 : Upper (D 4) (R 4) [6,12,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b366
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 88 400 51 83 147 275), lower := (rows 7 14 44 88 400 32 64 128 256), losses := [] }

theorem u367 : Upper (D 4) (R 4) [6,12,40,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b367
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 44 200 273 51 83 147 275), lower := (rows 7 14 44 200 273 32 64 128 256), losses := [] }

theorem u368 : Upper (D 4) (R 4) [6,12,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b368
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 25 88 419 451 387 387), lower := (rows 7 14 52 25 88 32 64 128 256), losses := [] }

theorem u369 : Upper (D 4) (R 4) [6,12,48,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b369
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 25 208 299 331 395 267), lower := (rows 7 14 52 25 208 32 64 128 256), losses := [] }

theorem u370 : Upper (D 4) (R 4) [6,12,48,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b370
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 73 145 314 346 410 282), lower := (rows 7 14 52 73 145 32 64 128 256), losses := [] }

theorem u371 : Upper (D 4) (R 4) [6,12,48,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b371
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 73 146 313 345 409 281), lower := (rows 7 14 52 73 146 32 64 128 256), losses := [] }

theorem u372 : Upper (D 4) (R 4) [6,12,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b372
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 73 152 307 339 403 275), lower := (rows 7 14 52 73 152 32 64 128 256), losses := [] }

theorem u373 : Upper (D 4) (R 4) [6,12,48,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b373
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 73 400 59 91 155 283), lower := (rows 7 14 52 73 400 32 64 128 256), losses := [] }

theorem u374 : Upper (D 4) (R 4) [6,12,48,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b374
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 74 25 433 465 401 401), lower := (rows 7 14 52 74 25 32 64 128 256), losses := [] }

theorem u375 : Upper (D 4) (R 4) [6,12,48,66,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b375
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 74 145 313 345 409 281), lower := (rows 7 14 52 74 145 32 64 128 256), losses := [] }

theorem u376 : Upper (D 4) (R 4) [6,12,48,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b376
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 74 152 305 337 401 273), lower := (rows 7 14 52 74 152 32 64 128 256), losses := [] }

theorem u377 : Upper (D 4) (R 4) [6,12,48,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b377
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 74 400 57 89 153 281), lower := (rows 7 14 52 74 400 32 64 128 256), losses := [] }

theorem u378 : Upper (D 4) (R 4) [6,12,48,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b378
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 88 25 419 451 387 387), lower := (rows 7 14 52 88 25 32 64 128 256), losses := [] }

theorem u379 : Upper (D 4) (R 4) [6,12,48,80,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b379
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 88 145 299 331 395 267), lower := (rows 7 14 52 88 145 32 64 128 256), losses := [] }

theorem u380 : Upper (D 4) (R 4) [6,12,48,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b380
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 88 152 291 323 387 259), lower := (rows 7 14 52 88 152 32 64 128 256), losses := [] }

theorem u381 : Upper (D 4) (R 4) [6,12,48,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b381
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 88 400 43 75 139 267), lower := (rows 7 14 52 88 400 32 64 128 256), losses := [] }

theorem u382 : Upper (D 4) (R 4) [6,12,48,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b382
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 200 25 307 339 403 275), lower := (rows 7 14 52 200 25 32 64 128 256), losses := [] }

theorem u383 : Upper (D 4) (R 4) [6,12,48,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b383
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 200 273 59 91 155 283), lower := (rows 7 14 52 200 273 32 64 128 256), losses := [] }

theorem u384 : Upper (D 4) (R 4) [6,12,48,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b384
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 200 274 57 89 153 281), lower := (rows 7 14 52 200 274 32 64 128 256), losses := [] }

theorem u385 : Upper (D 4) (R 4) [6,12,48,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b385
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 52 200 280 51 83 147 275), lower := (rows 7 14 52 200 280 32 64 128 256), losses := [] }

theorem u386 : Upper (D 4) (R 4) [6,12,48,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b386
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 25 146 313 345 409 281), lower := (rows 7 14 100 25 146 32 64 128 256), losses := [] }

theorem u387 : Upper (D 4) (R 4) [6,12,96,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b387
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 25 152 307 339 403 275), lower := (rows 7 14 100 25 152 32 64 128 256), losses := [] }

theorem u388 : Upper (D 4) (R 4) [6,12,96,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b388
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 25 400 59 91 155 283), lower := (rows 7 14 100 25 400 32 64 128 256), losses := [] }

theorem u389 : Upper (D 4) (R 4) [6,12,96,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b389
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 137 274 57 89 153 281), lower := (rows 7 14 100 137 274 32 64 128 256), losses := [] }

theorem u390 : Upper (D 4) (R 4) [6,12,96,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b390
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 137 280 51 83 147 275), lower := (rows 7 14 100 137 280 32 64 128 256), losses := [] }

theorem u391 : Upper (D 4) (R 4) [6,12,96,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b391
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 138 25 305 337 401 273), lower := (rows 7 14 100 138 25 32 64 128 256), losses := [] }

theorem u392 : Upper (D 4) (R 4) [6,12,96,130,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b392
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 138 273 57 89 153 281), lower := (rows 7 14 100 138 273 32 64 128 256), losses := [] }

theorem u393 : Upper (D 4) (R 4) [6,12,96,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b393
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 138 280 49 81 145 273), lower := (rows 7 14 100 138 280 32 64 128 256), losses := [] }

theorem u394 : Upper (D 4) (R 4) [6,12,96,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b394
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 152 25 307 339 403 275), lower := (rows 7 14 100 152 25 32 64 128 256), losses := [] }

theorem u395 : Upper (D 4) (R 4) [6,12,96,144,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b395
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 152 273 59 91 155 283), lower := (rows 7 14 100 152 273 32 64 128 256), losses := [] }

theorem u396 : Upper (D 4) (R 4) [6,12,96,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b396
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 152 274 57 89 153 281), lower := (rows 7 14 100 152 274 32 64 128 256), losses := [] }

theorem u397 : Upper (D 4) (R 4) [6,12,96,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b397
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 152 280 51 83 147 275), lower := (rows 7 14 100 152 280 32 64 128 256), losses := [] }

theorem u398 : Upper (D 4) (R 4) [6,12,96,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b398
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 100 392 25 51 83 147 275), lower := (rows 7 14 100 392 25 32 64 128 256), losses := [] }

theorem u399 : Upper (D 4) (R 4) [6,12,96,384,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b399
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 424, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 28 41 82 421 453 389 389), lower := (rows 7 26 28 41 82 32 64 128 256), losses := [] }

theorem u400 : Upper (D 4) (R 4) [6,24,24,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b400
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 464, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 28 41 208 295 327 391 263), lower := (rows 7 26 28 41 208 32 64 128 256), losses := [] }

theorem u401 : Upper (D 4) (R 4) [6,24,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b401
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 28 42 208 293 325 389 261), lower := (rows 7 26 28 42 208 32 64 128 256), losses := [] }

theorem u402 : Upper (D 4) (R 4) [6,24,24,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b402
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 28 104 400 39 71 135 263), lower := (rows 7 26 28 104 400 32 64 128 256), losses := [] }

theorem u403 : Upper (D 4) (R 4) [6,24,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b403
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r404 : Route 9 := (fun mask => (mask,id))

def c404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u404 : Upper (D 4) (R 4) [6,24,33,65,130] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,130] 13 (by decide) (choices 1) [4,8,16,256] r404 c404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u66
  · exact u67
  · exact u68
  · exact u69

def b405 : PairBound 9 := { available := 282, camps := [], pairs := [(1,0)], upper := (rows 7 26 37 73 148 314 346 410 282), lower := (rows 7 26 37 73 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 42 74 138 266), good := (rows 502 506 52 506 148 32 64 128 256) }] }

theorem u405 : Upper (D 4) (R 4) [6,24,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b405
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 293, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 73 152 310 342 406 278), lower := (rows 7 26 37 73 152 32 64 128 256), losses := [] }

theorem u406 : Upper (D 4) (R 4) [6,24,33,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b406
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r407 : Route 9 := (fun mask => (mask,id))

def c407 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u407 : Upper (D 4) (R 4) [6,24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,384] 13 (by decide) (choices 1) [2,4,8,16] r407 c407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u70
  · exact u71
  · exact u72
  · exact u73

def r408 : Route 9 := (fun mask => (mask,id))

def c408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u408 : Upper (D 4) (R 4) [6,24,33,66,132] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,132] 13 (by decide) (choices 1) [1,8,16,256] r408 c408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u74
  · exact u75
  · exact u76
  · exact u77

def b409 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 293, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 74 152 309 341 405 277), lower := (rows 7 26 37 74 152 32 64 128 256), losses := [] }

theorem u409 : Upper (D 4) (R 4) [6,24,33,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b409
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r410 : Route 9 := (fun mask => (mask,id))

def c410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u410 : Upper (D 4) (R 4) [6,24,33,66,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,384] 13 (by decide) (choices 1) [1,4,8,16] r410 c410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u78
  · exact u79
  · exact u80
  · exact u81

def b411 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 293, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 76 152 307 339 403 275), lower := (rows 7 26 37 76 152 32 64 128 256), losses := [] }

theorem u411 : Upper (D 4) (R 4) [6,24,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b411
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r412 : Route 9 := (fun mask => (mask,id))

def c412 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u412 : Upper (D 4) (R 4) [6,24,33,68,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68,384] 13 (by decide) (choices 1) [1,2,8,16] r412 c412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u82
  · exact u83
  · exact u84
  · exact u85

def b413 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 293, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 37 88 152 295 327 391 263), lower := (rows 7 26 37 88 152 32 64 128 256), losses := [] }

theorem u413 : Upper (D 4) (R 4) [6,24,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b413
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 15, camps := [{ cop := 1, region := 37, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 37 88 400 47 79 143 271), lower := (rows 7 26 37 88 400 32 64 128 256), losses := [] }

theorem u414 : Upper (D 4) (R 4) [6,24,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b414
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 38 73 148 313 345 409 281), lower := (rows 7 26 38 73 148 32 64 128 256), losses := [] }

theorem u415 : Upper (D 4) (R 4) [6,24,34,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b415
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 38 73 400 61 93 157 285), lower := (rows 7 26 38 73 400 32 64 128 256), losses := [] }

theorem u416 : Upper (D 4) (R 4) [6,24,34,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b416
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 38 76 400 57 89 153 281), lower := (rows 7 26 38 76 400 32 64 128 256), losses := [] }

theorem u417 : Upper (D 4) (R 4) [6,24,34,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b417
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 73 146 309 341 405 277), lower := (rows 7 26 44 73 146 32 64 128 256), losses := [] }

theorem u418 : Upper (D 4) (R 4) [6,24,40,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b418
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 73 148 307 339 403 275), lower := (rows 7 26 44 73 148 32 64 128 256), losses := [] }

theorem u419 : Upper (D 4) (R 4) [6,24,40,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b419
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P04
