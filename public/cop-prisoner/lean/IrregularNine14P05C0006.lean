import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0000

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 272, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 26 100 168 273 34 72 133 261), lower := (rows 7 26 100 168 273 34 72 128 256), losses := [] }

theorem u360 : Upper (D 5) (R 5) [6,24,96,160,257,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b360
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 7 26 100 168 276 33 65 138 266), lower := (rows 7 26 100 168 276 33 65 128 256), losses := [] }

theorem u361 : Upper (D 5) (R 5) [6,24,96,160,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b361
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 100 168 276 33 66 137 265), lower := (rows 7 26 100 168 276 33 66 128 256), losses := [] }

theorem u362 : Upper (D 5) (R 5) [6,24,96,160,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b362
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 26 100 168 276 33 72 131 259), lower := (rows 7 26 100 168 276 33 72 128 256), losses := [] }

theorem u363 : Upper (D 5) (R 5) [6,24,96,160,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b363
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 26 100 168 276 34 65 137 265), lower := (rows 7 26 100 168 276 34 65 128 256), losses := [] }

theorem u364 : Upper (D 5) (R 5) [6,24,96,160,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b364
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 7 26 100 168 276 34 72 129 257), lower := (rows 7 26 100 168 276 34 72 128 256), losses := [] }

theorem u365 : Upper (D 5) (R 5) [6,24,96,160,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b365
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 40, targets := 4 }], pairs := [(2,1),(3,2)], upper := (rows 7 26 196 42 276 33 65 168 296), lower := (rows 7 26 196 42 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 26 97 97 136 264), good := (rows 117 412 228 508 276 97 97 128 256) }] }

theorem u366 : Upper (D 5) (R 5) [6,24,192,34,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b366
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 26 196 42 276 33 72 161 289), lower := (rows 7 26 196 42 276 33 72 128 256), losses := [] }

theorem u367 : Upper (D 5) (R 5) [6,24,192,34,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b367
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m368_1 : Upper (D 5) (R 5) [6,24,192,34,260,1,32,1] 13 :=
  permutation_upper _ _ _ [6,24,192,34,260,1,1,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u32

theorem m368_8 : Upper (D 5) (R 5) [6,24,192,34,260,1,32,8] 13 :=
  permutation_upper _ _ _ [6,24,192,34,260,1,8,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33

def r368 : Route 9 := (fun mask => (mask,id))

def c368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u368 : Upper (D 5) (R 5) [6,24,192,34,260,1,32] 13 := by
  apply FastRouting.sound _ _ [6,24,192,34,260,1,32] 13 (by decide) (choices 1) [1,8] r368 c368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m368_1
  · exact m368_8

def b369 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 25 176 288 66 140 268), lower := (rows 7 35 76 25 176 288 66 128 256), losses := [] }

theorem u369 : Upper (D 5) (R 5) [6,33,72,17,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 25 176 288 68 138 266), lower := (rows 7 35 76 25 176 288 68 128 256), losses := [] }

theorem u370 : Upper (D 5) (R 5) [6,33,72,17,160,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b370
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 25 176 288 72 134 262), lower := (rows 7 35 76 25 176 288 72 128 256), losses := [] }

theorem u371 : Upper (D 5) (R 5) [6,33,72,17,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 26 148 288 65 168 296), lower := (rows 7 35 76 26 148 288 65 128 256), losses := [] }

theorem u372 : Upper (D 5) (R 5) [6,33,72,18,132,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b372
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 26 148 288 72 161 289), lower := (rows 7 35 76 26 148 288 72 128 256), losses := [] }

theorem u373 : Upper (D 5) (R 5) [6,33,72,18,132,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b373
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 26 148 288 96 137 265), lower := (rows 7 35 76 26 148 288 96 128 256), losses := [] }

theorem u374 : Upper (D 5) (R 5) [6,33,72,18,132,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b374
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 28 145 288 66 168 296), lower := (rows 7 35 76 28 145 288 66 128 256), losses := [] }

theorem u375 : Upper (D 5) (R 5) [6,33,72,20,129,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b375
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 28 145 288 72 162 290), lower := (rows 7 35 76 28 145 288 72 128 256), losses := [] }

theorem u376 : Upper (D 5) (R 5) [6,33,72,20,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 28 145 288 96 138 266), lower := (rows 7 35 76 28 145 288 96 128 256), losses := [] }

theorem u377 : Upper (D 5) (R 5) [6,33,72,20,129,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b377
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 76 28 146 288 65 168 296), lower := (rows 7 35 76 28 146 288 65 128 256), losses := [] }

theorem u378 : Upper (D 5) (R 5) [6,33,72,20,130,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b378
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 290, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 28 146 288 72 161 289), lower := (rows 7 35 76 28 146 288 72 128 256), losses := [] }

theorem u379 : Upper (D 5) (R 5) [6,33,72,20,130,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b379
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 28 146 288 96 137 265), lower := (rows 7 35 76 28 146 288 96 128 256), losses := [] }

theorem u380 : Upper (D 5) (R 5) [6,33,72,20,130,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 28 176 288 65 138 266), lower := (rows 7 35 76 28 176 288 65 128 256), losses := [] }

theorem u381 : Upper (D 5) (R 5) [6,33,72,20,160,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b381
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 28 176 288 66 137 265), lower := (rows 7 35 76 28 176 288 66 128 256), losses := [] }

theorem u382 : Upper (D 5) (R 5) [6,33,72,20,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b382
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 28 176 288 72 131 259), lower := (rows 7 35 76 28 176 288 72 128 256), losses := [] }

theorem u383 : Upper (D 5) (R 5) [6,33,72,20,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b383
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 56 145 288 66 140 268), lower := (rows 7 35 76 56 145 288 66 128 256), losses := [] }

theorem u384 : Upper (D 5) (R 5) [6,33,72,48,129,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 56 145 288 68 138 266), lower := (rows 7 35 76 56 145 288 68 128 256), losses := [] }

theorem u385 : Upper (D 5) (R 5) [6,33,72,48,129,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 56 145 288 72 134 262), lower := (rows 7 35 76 56 145 288 72 128 256), losses := [] }

theorem u386 : Upper (D 5) (R 5) [6,33,72,48,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 56 146 288 65 140 268), lower := (rows 7 35 76 56 146 288 65 128 256), losses := [] }

theorem u387 : Upper (D 5) (R 5) [6,33,72,48,130,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 56 146 288 68 137 265), lower := (rows 7 35 76 56 146 288 68 128 256), losses := [] }

theorem u388 : Upper (D 5) (R 5) [6,33,72,48,130,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 56 146 288 72 133 261), lower := (rows 7 35 76 56 146 288 72 128 256), losses := [] }

theorem u389 : Upper (D 5) (R 5) [6,33,72,48,130,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 56 148 288 65 138 266), lower := (rows 7 35 76 56 148 288 65 128 256), losses := [] }

theorem u390 : Upper (D 5) (R 5) [6,33,72,48,132,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 56 148 288 66 137 265), lower := (rows 7 35 76 56 148 288 66 128 256), losses := [] }

theorem u391 : Upper (D 5) (R 5) [6,33,72,48,132,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b391
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 8 }], pairs := [(0,3)], upper := (rows 7 35 76 56 148 288 72 131 259), lower := (rows 7 35 76 56 148 288 72 128 256), losses := [] }

theorem u392 : Upper (D 5) (R 5) [6,33,72,48,132,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 138 56 288 65 148 276), lower := (rows 7 35 76 138 56 288 65 128 256), losses := [] }

theorem u393 : Upper (D 5) (R 5) [6,33,72,130,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 138 56 288 68 145 273), lower := (rows 7 35 76 138 56 288 68 128 256), losses := [] }

theorem u394 : Upper (D 5) (R 5) [6,33,72,130,40,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 7 35 76 138 56 288 80 133 261), lower := (rows 7 35 76 138 56 288 80 128 256), losses := [] }

theorem u395 : Upper (D 5) (R 5) [6,33,72,130,40,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 138 280 48 65 164 292), lower := (rows 7 35 76 138 280 48 65 128 256), losses := [] }

theorem u396 : Upper (D 5) (R 5) [6,33,72,130,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 138 280 48 68 161 289), lower := (rows 7 35 76 138 280 48 68 128 256), losses := [] }

theorem u397 : Upper (D 5) (R 5) [6,33,72,130,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 138 280 48 96 133 261), lower := (rows 7 35 76 138 280 48 96 128 256), losses := [] }

theorem u398 : Upper (D 5) (R 5) [6,33,72,130,264,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 140 26 288 65 176 304), lower := (rows 7 35 76 140 26 288 65 128 256), losses := [] }

theorem u399 : Upper (D 5) (R 5) [6,33,72,132,10,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 76 140 26 288 80 161 289), lower := (rows 7 35 76 140 26 288 80 128 256), losses := [] }

theorem u400 : Upper (D 5) (R 5) [6,33,72,132,10,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b400
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 140 26 288 96 145 273), lower := (rows 7 35 76 140 26 288 96 128 256), losses := [] }

theorem u401 : Upper (D 5) (R 5) [6,33,72,132,10,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 140 56 288 65 146 274), lower := (rows 7 35 76 140 56 288 65 128 256), losses := [] }

theorem u402 : Upper (D 5) (R 5) [6,33,72,132,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 140 56 288 66 145 273), lower := (rows 7 35 76 140 56 288 66 128 256), losses := [] }

theorem u403 : Upper (D 5) (R 5) [6,33,72,132,40,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 7 35 76 140 56 288 80 131 259), lower := (rows 7 35 76 140 56 288 80 128 256), losses := [] }

theorem u404 : Upper (D 5) (R 5) [6,33,72,132,40,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 140 280 48 65 162 290), lower := (rows 7 35 76 140 280 48 65 128 256), losses := [] }

theorem u405 : Upper (D 5) (R 5) [6,33,72,132,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 140 280 48 66 161 289), lower := (rows 7 35 76 140 280 48 66 128 256), losses := [] }

theorem u406 : Upper (D 5) (R 5) [6,33,72,132,264,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 76 140 280 48 96 131 259), lower := (rows 7 35 76 140 280 48 96 128 256), losses := [] }

theorem u407 : Upper (D 5) (R 5) [6,33,72,132,264,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 76 152 274 40 65 164 292), lower := (rows 7 35 76 152 274 40 65 128 256), losses := [] }

theorem u408 : Upper (D 5) (R 5) [6,33,72,144,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 76 152 274 40 68 161 289), lower := (rows 7 35 76 152 274 40 68 128 256), losses := [] }

theorem u409 : Upper (D 5) (R 5) [6,33,72,144,258,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 76 152 274 40 96 133 261), lower := (rows 7 35 76 152 274 40 96 128 256), losses := [] }

theorem u410 : Upper (D 5) (R 5) [6,33,72,144,258,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 168 25 288 66 148 276), lower := (rows 7 35 76 168 25 288 66 128 256), losses := [] }

theorem u411 : Upper (D 5) (R 5) [6,33,72,160,9,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b411
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 168 25 288 68 146 274), lower := (rows 7 35 76 168 25 288 68 128 256), losses := [] }

theorem u412 : Upper (D 5) (R 5) [6,33,72,160,9,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 7 35 76 168 25 288 80 134 262), lower := (rows 7 35 76 168 25 288 80 128 256), losses := [] }

theorem u413 : Upper (D 5) (R 5) [6,33,72,160,9,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 168 280 48 65 134 262), lower := (rows 7 35 76 168 280 48 65 128 256), losses := [] }

theorem u414 : Upper (D 5) (R 5) [6,33,72,160,264,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 76 168 280 48 66 133 261), lower := (rows 7 35 76 168 280 48 66 128 256), losses := [] }

theorem u415 : Upper (D 5) (R 5) [6,33,72,160,264,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 442, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 76 168 280 48 68 131 259), lower := (rows 7 35 76 168 280 48 68 128 256), losses := [] }

theorem u416 : Upper (D 5) (R 5) [6,33,72,160,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b416
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 84 137 280 40 66 164 292), lower := (rows 7 35 84 137 280 40 66 128 256), losses := [] }

theorem u417 : Upper (D 5) (R 5) [6,33,80,129,264,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 137 280 40 68 162 290), lower := (rows 7 35 84 137 280 40 68 128 256), losses := [] }

theorem u418 : Upper (D 5) (R 5) [6,33,80,129,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 84 137 280 40 96 134 262), lower := (rows 7 35 84 137 280 40 96 128 256), losses := [] }

theorem u419 : Upper (D 5) (R 5) [6,33,80,129,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b419
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P05
