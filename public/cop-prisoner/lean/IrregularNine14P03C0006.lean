import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0000

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 14 69 137 112 160 66 145 273), lower := (rows 289 14 69 137 112 160 66 128 256), losses := [] }

theorem u360 : Upper (D 3) (R 3) [288,12,65,129,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b360
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 14 69 137 112 160 80 131 259), lower := (rows 289 14 69 137 112 160 80 128 256), losses := [] }

theorem u361 : Upper (D 3) (R 3) [288,12,65,129,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b361
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 168 145 96 65 146 274), lower := (rows 289 14 69 168 145 96 65 128 256), losses := [] }

theorem u362 : Upper (D 3) (R 3) [288,12,65,160,129,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b362
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 14 69 168 145 96 66 145 273), lower := (rows 289 14 69 168 145 96 66 128 256), losses := [] }

theorem u363 : Upper (D 3) (R 3) [288,12,65,160,129,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b363
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 14 69 168 145 96 80 131 259), lower := (rows 289 14 69 168 145 96 80 128 256), losses := [] }

theorem u364 : Upper (D 3) (R 3) [288,12,65,160,129,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 289 38 69 88 145 160 65 138 266), lower := (rows 289 38 69 88 145 160 65 128 256), losses := [] }

theorem u365 : Upper (D 3) (R 3) [288,36,65,80,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 38 69 88 145 160 66 137 265), lower := (rows 289 38 69 88 145 160 66 128 256), losses := [] }

theorem u366 : Upper (D 3) (R 3) [288,36,65,80,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b366
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 38 69 88 145 160 72 131 259), lower := (rows 289 38 69 88 145 160 72 128 256), losses := [] }

theorem u367 : Upper (D 3) (R 3) [288,36,65,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 104 176 33 448 448 448), lower := (rows 7 11 21 104 176 33 64 128 256), losses := [] }

theorem u368 : Upper (D 3) (R 3) [6,9,17,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 21 104 176 96 449 385 385), lower := (rows 7 11 21 104 176 96 64 128 256), losses := [] }

theorem u369 : Upper (D 3) (R 3) [6,9,17,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b369
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 21 104 176 288 193 193 449), lower := (rows 7 11 21 104 176 288 64 128 256), losses := [] }

theorem u370 : Upper (D 3) (R 3) [6,9,17,96,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b370
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 104 304 33 192 192 448), lower := (rows 7 11 21 104 304 33 64 128 256), losses := [] }

theorem u371 : Upper (D 3) (R 3) [6,9,17,96,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b371
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 21 104 304 96 193 129 385), lower := (rows 7 11 21 104 304 96 64 128 256), losses := [] }

theorem u372 : Upper (D 3) (R 3) [6,9,17,96,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b372
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r373 : Route 9 := (fun mask => (mask,id))

def c373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u373 : Upper (D 3) (R 3) [6,9,17,96,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,288,128] 13 (by decide) (choices 1) [1,128] r373 c373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b374 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 104 400 33 224 224 480), lower := (rows 7 11 21 104 400 33 64 128 256), losses := [] }

theorem u374 : Upper (D 3) (R 3) [6,9,17,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b374
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 21 104 400 96 225 161 417), lower := (rows 7 11 21 104 400 96 64 128 256), losses := [] }

theorem u375 : Upper (D 3) (R 3) [6,9,17,96,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b375
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m376_1 : Upper (D 3) (R 3) [6,9,17,96,384,128,1] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4

theorem m376_32 : Upper (D 3) (R 3) [6,9,17,96,384,128,32] 13 :=
  permutation_upper _ _ _ [6,9,17,96,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5

def r376 : Route 9 := (fun mask => (mask,id))

def c376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u376 : Upper (D 3) (R 3) [6,9,17,96,384,128] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384,128] 13 (by decide) (choices 1) [1,32] r376 c376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m376_1
  · exact m376_32

def b377 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 88 176 33 448 448 448), lower := (rows 7 11 37 88 176 33 64 128 256), losses := [] }

theorem u377 : Upper (D 3) (R 3) [6,9,33,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b377
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 88 176 96 449 385 385), lower := (rows 7 11 37 88 176 96 64 128 256), losses := [] }

theorem u378 : Upper (D 3) (R 3) [6,9,33,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b378
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 88 176 160 321 449 321), lower := (rows 7 11 37 88 176 160 64 128 256), losses := [] }

theorem u379 : Upper (D 3) (R 3) [6,9,33,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b379
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 37 88 176 288 193 193 449), lower := (rows 7 11 37 88 176 288 64 128 256), losses := [] }

theorem u380 : Upper (D 3) (R 3) [6,9,33,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b380
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 88 304 33 192 192 448), lower := (rows 7 11 37 88 304 33 64 128 256), losses := [] }

theorem u381 : Upper (D 3) (R 3) [6,9,33,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b381
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 88 304 96 193 129 385), lower := (rows 7 11 37 88 304 96 64 128 256), losses := [] }

theorem u382 : Upper (D 3) (R 3) [6,9,33,80,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b382
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r383 : Route 9 := (fun mask => (mask,id))

def c383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u383 : Upper (D 3) (R 3) [6,9,33,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,80,288,128] 13 (by decide) (choices 1) [1,128] r383 c383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b384 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 88 400 33 224 224 480), lower := (rows 7 11 37 88 400 33 64 128 256), losses := [] }

theorem u384 : Upper (D 3) (R 3) [6,9,33,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b384
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 88 400 96 225 161 417), lower := (rows 7 11 37 88 400 96 64 128 256), losses := [] }

theorem u385 : Upper (D 3) (R 3) [6,9,33,80,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b385
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 97, camps := [], pairs := [(0,6)], upper := (rows 7 11 37 88 400 160 97 225 353), lower := (rows 7 11 37 88 400 160 64 128 256), losses := [{ target := 6, region := (rows 11 10 12 8 16 176 0 128 256), good := (rows 7 15 37 63 432 160 0 160 256) }] }

theorem u386 : Upper (D 3) (R 3) [6,9,33,80,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b386
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 200 112 33 464 400 400), lower := (rows 7 11 37 200 112 33 64 128 256), losses := [] }

theorem u387 : Upper (D 3) (R 3) [6,9,33,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b387
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 7 11 37 200 112 48 449 385 385), lower := (rows 7 11 37 200 112 48 64 128 256), losses := [] }

theorem u388 : Upper (D 3) (R 3) [6,9,33,192,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b388
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 200 112 160 337 401 273), lower := (rows 7 11 37 200 112 160 64 128 256), losses := [] }

theorem u389 : Upper (D 3) (R 3) [6,9,33,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b389
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 11 37 200 112 288 209 145 401), lower := (rows 7 11 37 200 112 288 64 128 256), losses := [] }

theorem u390 : Upper (D 3) (R 3) [6,9,33,192,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b390
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 200 304 33 208 208 464), lower := (rows 7 11 37 200 304 33 64 128 256), losses := [] }

theorem u391 : Upper (D 3) (R 3) [6,9,33,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b391
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 37 200 304 48 193 193 449), lower := (rows 7 11 37 200 304 48 64 128 256), losses := [] }

theorem u392 : Upper (D 3) (R 3) [6,9,33,192,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b392
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 200 304 96 209 145 401), lower := (rows 7 11 37 200 304 96 64 128 256), losses := [] }

theorem u393 : Upper (D 3) (R 3) [6,9,33,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b393
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 200 336 33 240 176 432), lower := (rows 7 11 37 200 336 33 64 128 256), losses := [] }

theorem u394 : Upper (D 3) (R 3) [6,9,33,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b394
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 37 200 336 48 225 161 417), lower := (rows 7 11 37 200 336 48 64 128 256), losses := [] }

theorem u395 : Upper (D 3) (R 3) [6,9,33,192,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b395
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 200 336 160 113 177 305), lower := (rows 7 11 37 200 336 160 64 128 256), losses := [] }

theorem u396 : Upper (D 3) (R 3) [6,9,33,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b396
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 280 112 33 192 192 448), lower := (rows 7 11 37 280 112 33 64 128 256), losses := [] }

theorem u397 : Upper (D 3) (R 3) [6,9,33,272,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b397
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 280 112 96 193 129 385), lower := (rows 7 11 37 280 112 96 64 128 256), losses := [] }

theorem u398 : Upper (D 3) (R 3) [6,9,33,272,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b398
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r399 : Route 9 := (fun mask => (mask,id))

def c399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u399 : Upper (D 3) (R 3) [6,9,33,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,272,96,128] 13 (by decide) (choices 1) [1,128] r399 c399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8
  · exact u9

def b400 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 280 208 33 224 224 480), lower := (rows 7 11 37 280 208 33 64 128 256), losses := [] }

theorem u400 : Upper (D 3) (R 3) [6,9,33,272,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b400
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 161, camps := [], pairs := [(0,7)], upper := (rows 7 11 37 280 208 96 225 161 417), lower := (rows 7 11 37 280 208 96 64 128 256), losses := [{ target := 7, region := (rows 11 10 12 8 16 112 64 0 256), good := (rows 7 15 37 319 112 96 96 0 256) }] }

theorem u401 : Upper (D 3) (R 3) [6,9,33,272,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b401
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 328 112 33 208 144 400), lower := (rows 7 11 37 328 112 33 64 128 256), losses := [] }

theorem u402 : Upper (D 3) (R 3) [6,9,33,320,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b402
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 11 37 328 112 48 193 129 385), lower := (rows 7 11 37 328 112 48 64 128 256), losses := [] }

theorem u403 : Upper (D 3) (R 3) [6,9,33,320,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b403
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r404 : Route 9 := (fun mask => (mask,id))

def c404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u404 : Upper (D 3) (R 3) [6,9,33,320,96,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,96,128] 13 (by decide) (choices 1) [1,16,128] r404 c404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10
  · exact u11
  · exact u12

def b405 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 328 176 33 208 208 464), lower := (rows 7 11 37 328 176 33 64 128 256), losses := [] }

theorem u405 : Upper (D 3) (R 3) [6,9,33,320,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b405
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 11 37 328 176 48 193 193 449), lower := (rows 7 11 37 328 176 48 64 128 256), losses := [] }

theorem u406 : Upper (D 3) (R 3) [6,9,33,320,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b406
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 328 176 96 209 145 401), lower := (rows 7 11 37 328 176 96 64 128 256), losses := [] }

theorem u407 : Upper (D 3) (R 3) [6,9,33,320,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b407
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 328 176 160 81 209 337), lower := (rows 7 11 37 328 176 160 64 128 256), losses := [] }

theorem u408 : Upper (D 3) (R 3) [6,9,33,320,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b408
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 37 328 208 33 240 176 432), lower := (rows 7 11 37 328 208 33 64 128 256), losses := [] }

theorem u409 : Upper (D 3) (R 3) [6,9,33,320,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b409
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 11 37 328 208 48 225 161 417), lower := (rows 7 11 37 328 208 48 64 128 256), losses := [] }

theorem u410 : Upper (D 3) (R 3) [6,9,33,320,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b410
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r411 : Route 9 := (fun mask => (mask,id))

def c411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u411 : Upper (D 3) (R 3) [6,9,33,320,192,128] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,192,128] 13 (by decide) (choices 1) [1,16,32] r411 c411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13
  · exact u14
  · exact u15

def b412 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 7 11 52 200 273 33 224 224 480), lower := (rows 7 11 52 200 273 33 64 128 256), losses := [] }

theorem u412 : Upper (D 3) (R 3) [6,9,48,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b412
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r413 : Route 9 := (fun mask => (mask,id))

def c413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u413 : Upper (D 3) (R 3) [6,9,48,192,257,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257,64] 13 (by decide) (choices 1) [1,32,128] r413 c413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16
  · exact u17
  · exact u18

def r414 : Route 9 := (fun mask => (mask,id))

def c414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u414 : Upper (D 3) (R 3) [6,9,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,1] 13 (by decide) (choices 1) [1,32,128] r414 c414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19
  · exact u20
  · exact u21

def r415 : Route 9 := (fun mask => (mask,id))

def c415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u415 : Upper (D 3) (R 3) [6,9,48,192,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,128] 13 (by decide) (choices 1) [1,32] r415 c415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22
  · exact u23

def b416 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 7 11 52 328 145 33 224 224 480), lower := (rows 7 11 52 328 145 33 64 128 256), losses := [] }

theorem u416 : Upper (D 3) (R 3) [6,9,48,320,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b416
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r417 : Route 9 := (fun mask => (mask,id))

def c417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u417 : Upper (D 3) (R 3) [6,9,48,320,129,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,129,64] 13 (by decide) (choices 1) [1,32,128] r417 c417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24
  · exact u25
  · exact u26

def b418 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 328 145 160 97 225 353), lower := (rows 7 11 52 328 145 160 64 128 256), losses := [] }

theorem u418 : Upper (D 3) (R 3) [6,9,48,320,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b418
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r419 : Route 9 := (fun mask => (mask,id))

def c419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u419 : Upper (D 3) (R 3) [6,9,48,320,192,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,320,192,1] 13 (by decide) (choices 1) [1,32,128] r419 c419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27
  · exact u28
  · exact u29

#print axioms u419
end Delivery.IrregularNine14.P03
