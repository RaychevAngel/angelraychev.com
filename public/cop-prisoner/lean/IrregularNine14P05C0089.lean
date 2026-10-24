import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0033

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5340 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 37 76 49 426 458 394 394), lower := (rows 7 26 37 76 49 32 64 128 256), losses := [] }

theorem u5340 : Upper (D 5) (R 5) [6,24,33,68,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5340
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5341 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 76 50 425 457 393 393), lower := (rows 7 26 37 76 50 32 64 128 256), losses := [] }

theorem u5341 : Upper (D 5) (R 5) [6,24,33,68,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5341
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5342 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 76 56 419 451 387 387), lower := (rows 7 26 37 76 56 32 64 128 256), losses := [] }

theorem u5342 : Upper (D 5) (R 5) [6,24,33,68,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5342
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5343 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 76 145 298 362 426 298), lower := (rows 7 26 37 76 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 51 83 147 275), good := (rows 494 506 492 76 506 32 64 128 256) }] }

theorem u5343 : Upper (D 5) (R 5) [6,24,33,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5343
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 76 146 297 361 425 297), lower := (rows 7 26 37 76 146 32 64 128 256), losses := [] }

theorem u5344 : Upper (D 5) (R 5) [6,24,33,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5344
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5345 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 76 152 291 355 419 291), lower := (rows 7 26 37 76 152 32 64 128 256), losses := [] }

theorem u5345 : Upper (D 5) (R 5) [6,24,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5345
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5346 : Route 9 := (fun mask => (mask,id))

def c5346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u5346 : Upper (D 5) (R 5) [6,24,33,68,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68,160] 13 (by decide) (choices 1) [1,2,8,256] r5346 c5346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1999
  · exact u2000
  · exact u2001
  · exact u2002

def r5347 : Route 9 := (fun mask => (mask,id))

def c5347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5347 : Upper (D 5) (R 5) [6,24,33,68,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68,384] 13 (by decide) (choices 1) [1,2,8] r5347 c5347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2003
  · exact u2004
  · exact u2005

def b5348 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 37 104 19 428 460 396 396), lower := (rows 7 26 37 104 19 32 64 128 256), losses := [] }

theorem u5348 : Upper (D 5) (R 5) [6,24,33,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5348
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 394, camps := [{ cop := 4, region := 490, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 104 21 426 458 394 394), lower := (rows 7 26 37 104 21 32 64 128 256), losses := [] }

theorem u5349 : Upper (D 5) (R 5) [6,24,33,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5349
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5350 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 104 22 425 457 393 393), lower := (rows 7 26 37 104 22 32 64 128 256), losses := [] }

theorem u5350 : Upper (D 5) (R 5) [6,24,33,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5350
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5351 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 104 25 422 454 390 390), lower := (rows 7 26 37 104 25 32 64 128 256), losses := [] }

theorem u5351 : Upper (D 5) (R 5) [6,24,33,96,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5351
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5352 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 104 26 421 453 389 389), lower := (rows 7 26 37 104 26 32 64 128 256), losses := [] }

theorem u5352 : Upper (D 5) (R 5) [6,24,33,96,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5352
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5353 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 421, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 104 28 419 451 387 387), lower := (rows 7 26 37 104 28 32 64 128 256), losses := [] }

theorem u5353 : Upper (D 5) (R 5) [6,24,33,96,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5353
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5354 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 360, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 104 145 302 334 398 270), lower := (rows 7 26 37 104 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 26 492 104 506 32 64 128 256) }] }

theorem u5354 : Upper (D 5) (R 5) [6,24,33,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5354
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5355 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 104 146 301 333 397 269), lower := (rows 7 26 37 104 146 32 64 128 256), losses := [] }

theorem u5355 : Upper (D 5) (R 5) [6,24,33,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5355
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5356 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 360, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 104 148 299 331 395 267), lower := (rows 7 26 37 104 148 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 33 65 129 257), good := (rows 491 26 489 104 154 32 64 128 256) }] }

theorem u5356 : Upper (D 5) (R 5) [6,24,33,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5356
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5357 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 104 152 295 327 391 263), lower := (rows 7 26 37 104 152 32 64 128 256), losses := [] }

theorem u5357 : Upper (D 5) (R 5) [6,24,33,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5357
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5358 : Route 9 := (fun mask => (mask,id))

def c5358 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5358 : Upper (D 5) (R 5) [6,24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,384] 13 (by decide) (choices 1) [1,2,4,8] r5358 c5358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2006
  · exact u2007
  · exact u2008
  · exact u2009

def b5359 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 26 37 200 19 300 364 428 300), lower := (rows 7 26 37 200 19 32 64 128 256), losses := [] }

theorem u5359 : Upper (D 5) (R 5) [6,24,33,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5359
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5360 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 490, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 200 21 298 362 426 298), lower := (rows 7 26 37 200 21 32 64 128 256), losses := [] }

theorem u5360 : Upper (D 5) (R 5) [6,24,33,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5361 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 200 22 297 361 425 297), lower := (rows 7 26 37 200 22 32 64 128 256), losses := [] }

theorem u5361 : Upper (D 5) (R 5) [6,24,33,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5362 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 200 25 294 358 422 294), lower := (rows 7 26 37 200 25 32 64 128 256), losses := [] }

theorem u5362 : Upper (D 5) (R 5) [6,24,33,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5363 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 200 26 293 357 421 293), lower := (rows 7 26 37 200 26 32 64 128 256), losses := [] }

theorem u5363 : Upper (D 5) (R 5) [6,24,33,192,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5364 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 293, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 37 200 28 291 355 419 291), lower := (rows 7 26 37 200 28 32 64 128 256), losses := [] }

theorem u5364 : Upper (D 5) (R 5) [6,24,33,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5365 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 37 200 49 302 334 398 270), lower := (rows 7 26 37 200 49 32 64 128 256), losses := [] }

theorem u5365 : Upper (D 5) (R 5) [6,24,33,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5366 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 200 50 301 333 397 269), lower := (rows 7 26 37 200 50 32 64 128 256), losses := [] }

theorem u5366 : Upper (D 5) (R 5) [6,24,33,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5367 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 26 37 200 52 299 331 395 267), lower := (rows 7 26 37 200 52 32 64 128 256), losses := [] }

theorem u5367 : Upper (D 5) (R 5) [6,24,33,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5367
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5368 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 200 56 295 327 391 263), lower := (rows 7 26 37 200 56 32 64 128 256), losses := [] }

theorem u5368 : Upper (D 5) (R 5) [6,24,33,192,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5368
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5369 : PairBound 9 := { available := 46, camps := [{ cop := 0, region := 232, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 37 200 273 46 110 174 302), lower := (rows 7 26 37 200 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 26 492 200 506 32 64 128 256) }] }

theorem u5369 : Upper (D 5) (R 5) [6,24,33,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5370 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 37 200 274 45 109 173 301), lower := (rows 7 26 37 200 274 32 64 128 256), losses := [] }

theorem u5370 : Upper (D 5) (R 5) [6,24,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5371 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 232, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 26 37 200 276 43 107 171 299), lower := (rows 7 26 37 200 276 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 33 65 129 257), good := (rows 491 26 489 200 282 32 64 128 256) }] }

theorem u5371 : Upper (D 5) (R 5) [6,24,33,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5372 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 2, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 37 200 280 39 103 167 295), lower := (rows 7 26 37 200 280 32 64 128 256), losses := [] }

theorem u5372 : Upper (D 5) (R 5) [6,24,33,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5373 : Route 9 := (fun mask => (mask,id))

def c5373 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5373 : Upper (D 5) (R 5) [6,24,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,288] 13 (by decide) (choices 1) [1,2,4,8] r5373 c5373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2010
  · exact u2011
  · exact u2012
  · exact u2013

def b5374 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 26 44 73 19 420 484 420 420), lower := (rows 7 26 44 73 19 32 64 128 256), losses := [] }

theorem u5374 : Upper (D 5) (R 5) [6,24,40,65,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 73 21 418 482 418 418), lower := (rows 7 26 44 73 21 32 64 128 256), losses := [] }

theorem u5375 : Upper (D 5) (R 5) [6,24,40,65,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5376 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 73 22 417 481 417 417), lower := (rows 7 26 44 73 22 32 64 128 256), losses := [] }

theorem u5376 : Upper (D 5) (R 5) [6,24,40,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5377 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5),(4,3)], upper := (rows 7 26 44 73 49 422 454 390 390), lower := (rows 7 26 44 73 49 32 64 128 256), losses := [] }

theorem u5377 : Upper (D 5) (R 5) [6,24,40,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5378 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 44 73 50 421 453 389 389), lower := (rows 7 26 44 73 50 32 64 128 256), losses := [] }

theorem u5378 : Upper (D 5) (R 5) [6,24,40,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5379 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 73 52 419 451 387 387), lower := (rows 7 26 44 73 52 32 64 128 256), losses := [] }

theorem u5379 : Upper (D 5) (R 5) [6,24,40,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5379
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5380 : PairBound 9 := { available := 294, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 1, region := 292, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 26 44 73 145 294 358 422 294), lower := (rows 7 26 44 73 145 32 64 128 256), losses := [] }

theorem u5380 : Upper (D 5) (R 5) [6,24,40,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5381 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 44 73 146 293 357 421 293), lower := (rows 7 26 44 73 146 32 64 128 256), losses := [] }

theorem u5381 : Upper (D 5) (R 5) [6,24,40,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5381
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 360, targets := 4 },{ cop := 0, region := 432, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 44 73 148 291 355 419 291), lower := (rows 7 26 44 73 148 32 64 128 256), losses := [] }

theorem u5382 : Upper (D 5) (R 5) [6,24,40,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5382
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 0, region := 328, targets := 32 }], pairs := [(3,5),(4,3)], upper := (rows 7 26 44 73 176 295 327 391 263), lower := (rows 7 26 44 73 176 32 64 128 256), losses := [] }

theorem u5383 : Upper (D 5) (R 5) [6,24,40,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5384 : Route 9 := (fun mask => (mask,id))

def c5384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5384 : Upper (D 5) (R 5) [6,24,40,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,40,65,384] 13 (by decide) (choices 1) [1,2,4] r5384 c5384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2014
  · exact u2015
  · exact u2016

def b5385 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 200 19 293 357 421 293), lower := (rows 7 26 44 200 19 32 64 128 256), losses := [] }

theorem u5385 : Upper (D 5) (R 5) [6,24,40,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 200 21 291 355 419 291), lower := (rows 7 26 44 200 21 32 64 128 256), losses := [] }

theorem u5386 : Upper (D 5) (R 5) [6,24,40,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5387 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 19, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 200 22 289 353 417 289), lower := (rows 7 26 44 200 22 32 64 128 256), losses := [] }

theorem u5387 : Upper (D 5) (R 5) [6,24,40,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5388 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5),(4,3)], upper := (rows 7 26 44 200 49 295 327 391 263), lower := (rows 7 26 44 200 49 32 64 128 256), losses := [] }

theorem u5388 : Upper (D 5) (R 5) [6,24,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5389 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 44 200 50 293 325 389 261), lower := (rows 7 26 44 200 50 32 64 128 256), losses := [] }

theorem u5389 : Upper (D 5) (R 5) [6,24,40,192,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5390 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 26 44 200 52 291 323 387 259), lower := (rows 7 26 44 200 52 32 64 128 256), losses := [] }

theorem u5390 : Upper (D 5) (R 5) [6,24,40,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r5391 : Route 9 := (fun mask => (mask,id))

def c5391 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5391 : Upper (D 5) (R 5) [6,24,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,24,40,192,257] 13 (by decide) (choices 1) [1,2,4] r5391 c5391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2017
  · exact u2018
  · exact u2019

def b5392 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 44 200 274 37 101 165 293), lower := (rows 7 26 44 200 274 32 64 128 256), losses := [] }

theorem u5392 : Upper (D 5) (R 5) [6,24,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 232, targets := 4 },{ cop := 0, region := 304, targets := 8 }], pairs := [(3,2),(4,3)], upper := (rows 7 26 44 200 276 35 99 163 291), lower := (rows 7 26 44 200 276 32 64 128 256), losses := [] }

theorem u5393 : Upper (D 5) (R 5) [6,24,40,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5),(4,3)], upper := (rows 7 26 44 200 304 39 71 135 263), lower := (rows 7 26 44 200 304 32 64 128 256), losses := [] }

theorem u5394 : Upper (D 5) (R 5) [6,24,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 26 69 41 22 424 488 424 424), lower := (rows 7 26 69 41 22 32 64 128 256), losses := [] }

theorem u5395 : Upper (D 5) (R 5) [6,24,65,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5396 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 41 26 420 484 420 420), lower := (rows 7 26 69 41 26 32 64 128 256), losses := [] }

theorem u5396 : Upper (D 5) (R 5) [6,24,65,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5397 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 485, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 69 41 28 418 482 418 418), lower := (rows 7 26 69 41 28 32 64 128 256), losses := [] }

theorem u5397 : Upper (D 5) (R 5) [6,24,65,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5398 : PairBound 9 := { available := 396, camps := [{ cop := 3, region := 18, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 26 69 41 50 428 460 396 396), lower := (rows 7 26 69 41 50 32 64 128 256), losses := [] }

theorem u5398 : Upper (D 5) (R 5) [6,24,65,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b5399 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 26 69 41 52 426 458 394 394), lower := (rows 7 26 69 41 52 32 64 128 256), losses := [] }

theorem u5399 : Upper (D 5) (R 5) [6,24,65,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b5399
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P05
