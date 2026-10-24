import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0000

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 305 82 69 138 144 34 72 164 292), lower := (rows 305 82 69 138 144 34 72 128 256), losses := [] }

theorem u360 : Upper (D 1) (R 1) [304,80,65,130,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b360
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 69 138 144 34 96 140 268), lower := (rows 305 82 69 138 144 34 96 128 256), losses := [] }

theorem u361 : Upper (D 1) (R 1) [304,80,65,130,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b361
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 140 144 34 66 168 296), lower := (rows 305 82 69 140 144 34 66 128 256), losses := [] }

theorem u362 : Upper (D 1) (R 1) [304,80,65,132,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 82 69 140 144 34 72 162 290), lower := (rows 305 82 69 140 144 34 72 128 256), losses := [] }

theorem u363 : Upper (D 1) (R 1) [304,80,65,132,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 69 140 144 34 96 138 266), lower := (rows 305 82 69 140 144 34 96 128 256), losses := [] }

theorem u364 : Upper (D 1) (R 1) [304,80,65,132,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 69 168 144 34 66 140 268), lower := (rows 305 82 69 168 144 34 66 128 256), losses := [] }

theorem u365 : Upper (D 1) (R 1) [304,80,65,160,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b365
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 82 69 168 144 34 68 138 266), lower := (rows 305 82 69 168 144 34 68 128 256), losses := [] }

theorem u366 : Upper (D 1) (R 1) [304,80,65,160,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 82 69 168 144 34 72 134 262), lower := (rows 305 82 69 168 144 34 72 128 256), losses := [] }

theorem u367 : Upper (D 1) (R 1) [304,80,65,160,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b367
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 417, targets := 2 }], pairs := [(0,1)], upper := (rows 305 194 13 14 80 160 66 176 304), lower := (rows 305 194 13 14 80 160 66 128 256), losses := [] }

theorem u368 : Upper (D 1) (R 1) [304,192,9,6,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b368
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 162, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 13 14 80 160 80 162 290), lower := (rows 305 194 13 14 80 160 80 128 256), losses := [] }

theorem u369 : Upper (D 1) (R 1) [304,192,9,6,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 305 194 13 14 80 160 96 146 274), lower := (rows 305 194 13 14 80 160 96 128 256), losses := [] }

theorem u370 : Upper (D 1) (R 1) [304,192,9,6,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 15 259 52 200 18 96 240 176 432), lower := (rows 15 259 52 200 18 96 64 128 256), losses := [] }

theorem u371 : Upper (D 1) (R 1) [14,257,48,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 15 259 52 200 48 96 210 146 402), lower := (rows 15 259 52 200 48 96 64 128 256), losses := [] }

theorem u372 : Upper (D 1) (R 1) [14,257,48,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 15 259 52 200 80 160 114 178 306), lower := (rows 15 259 52 200 80 160 64 128 256), losses := [] }

theorem u373 : Upper (D 1) (R 1) [14,257,48,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b373
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 212, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 100 296 144 34 208 208 464), lower := (rows 23 11 100 296 144 34 64 128 256), losses := [] }

theorem u374 : Upper (D 1) (R 1) [22,9,96,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b374
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r375 : Route 9 := (fun mask => (mask,id))

def c375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u375 : Upper (D 1) (R 1) [22,9,96,288,128,16] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288,128,16] 13 (by decide) (choices 1) [2,128] r375 c375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b376 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 23 11 100 296 144 96 210 146 402), lower := (rows 23 11 100 296 144 96 64 128 256), losses := [] }

theorem u376 : Upper (D 1) (R 1) [22,9,96,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r377 : Route 9 := (fun mask => (mask,id))

def c377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u377 : Upper (D 1) (R 1) [22,9,96,288,128,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288,128,128] 13 (by decide) (choices 1) [2,16] r377 c377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2
  · exact u3

def b378 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 468, targets := 2 }], pairs := [(2,1)], upper := (rows 23 11 292 104 144 34 208 208 464), lower := (rows 23 11 292 104 144 34 64 128 256), losses := [] }

theorem u378 : Upper (D 1) (R 1) [22,9,288,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r379 : Route 9 := (fun mask => (mask,id))

def c379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u379 : Upper (D 1) (R 1) [22,9,288,96,128,16] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96,128,16] 13 (by decide) (choices 1) [2,128] r379 c379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4
  · exact u5

def b380 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 23 11 292 104 144 96 210 146 402), lower := (rows 23 11 292 104 144 96 64 128 256), losses := [] }

theorem u380 : Upper (D 1) (R 1) [22,9,288,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r381 : Route 9 := (fun mask => (mask,id))

def c381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u381 : Upper (D 1) (R 1) [22,9,288,96,128,128] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96,128,128] 13 (by decide) (choices 1) [2,16] r381 c381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6
  · exact u7

def b382 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 76 296 144 34 208 208 464), lower := (rows 23 35 76 296 144 34 64 128 256), losses := [] }

theorem u382 : Upper (D 1) (R 1) [22,33,72,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 296 144 48 194 194 450), lower := (rows 23 35 76 296 144 48 64 128 256), losses := [] }

theorem u383 : Upper (D 1) (R 1) [22,33,72,288,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 23 35 76 296 144 96 210 146 402), lower := (rows 23 35 76 296 144 96 64 128 256), losses := [] }

theorem u384 : Upper (D 1) (R 1) [22,33,72,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b384
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 82, camps := [], pairs := [(1,4)], upper := (rows 23 35 76 296 144 160 82 210 338), lower := (rows 23 35 76 296 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 76 296 160 160 64 160 256) }] }

theorem u385 : Upper (D 1) (R 1) [22,33,72,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b385
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 268 104 144 34 208 208 464), lower := (rows 23 35 268 104 144 34 64 128 256), losses := [] }

theorem u386 : Upper (D 1) (R 1) [22,33,264,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b386
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 268 104 144 48 194 194 450), lower := (rows 23 35 268 104 144 48 64 128 256), losses := [] }

theorem u387 : Upper (D 1) (R 1) [22,33,264,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b387
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 23 35 268 104 144 96 210 146 402), lower := (rows 23 35 268 104 144 96 64 128 256), losses := [] }

theorem u388 : Upper (D 1) (R 1) [22,33,264,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 82, camps := [], pairs := [(1,4)], upper := (rows 23 35 268 104 144 160 82 210 338), lower := (rows 23 35 268 104 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 268 104 160 160 64 160 256) }] }

theorem u389 : Upper (D 1) (R 1) [22,33,264,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 56 144 34 200 200 456), lower := (rows 23 35 324 56 144 34 64 128 256), losses := [] }

theorem u390 : Upper (D 1) (R 1) [22,33,320,48,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 23 35 324 56 144 40 194 194 450), lower := (rows 23 35 324 56 144 40 64 128 256), losses := [] }

theorem u391 : Upper (D 1) (R 1) [22,33,320,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b391
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 23 35 324 56 144 96 202 138 394), lower := (rows 23 35 324 56 144 96 64 128 256), losses := [] }

theorem u392 : Upper (D 1) (R 1) [22,33,320,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 23 35 324 56 144 160 74 202 330), lower := (rows 23 35 324 56 144 160 64 128 256), losses := [] }

theorem u393 : Upper (D 1) (R 1) [22,33,320,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b393
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 88 144 34 232 168 424), lower := (rows 23 35 324 88 144 34 64 128 256), losses := [] }

theorem u394 : Upper (D 1) (R 1) [22,33,320,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b394
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 23 35 324 88 144 40 226 162 418), lower := (rows 23 35 324 88 144 40 64 128 256), losses := [] }

theorem u395 : Upper (D 1) (R 1) [22,33,320,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 42, camps := [], pairs := [(1,4)], upper := (rows 23 35 324 88 144 160 106 170 298), lower := (rows 23 35 324 88 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 324 104 160 160 64 160 256) }] }

theorem u396 : Upper (D 1) (R 1) [22,33,320,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b396
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 104 144 34 216 152 408), lower := (rows 23 35 324 104 144 34 64 128 256), losses := [] }

theorem u397 : Upper (D 1) (R 1) [22,33,320,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 23 35 324 104 144 40 210 146 402), lower := (rows 23 35 324 104 144 40 64 128 256), losses := [] }

theorem u398 : Upper (D 1) (R 1) [22,33,320,96,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 104 144 48 202 138 394), lower := (rows 23 35 324 104 144 48 64 128 256), losses := [] }

theorem u399 : Upper (D 1) (R 1) [22,33,320,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b399
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 26, camps := [], pairs := [(1,4)], upper := (rows 23 35 324 104 144 160 90 154 282), lower := (rows 23 35 324 104 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 39 35 324 104 160 160 64 160 256) }] }

theorem u400 : Upper (D 1) (R 1) [22,33,320,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b400
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 168 144 34 88 216 344), lower := (rows 23 35 324 168 144 34 64 128 256), losses := [] }

theorem u401 : Upper (D 1) (R 1) [22,33,320,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b401
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 23 35 324 168 144 40 82 210 338), lower := (rows 23 35 324 168 144 40 64 128 256), losses := [] }

theorem u402 : Upper (D 1) (R 1) [22,33,320,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b402
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 168 144 48 74 202 330), lower := (rows 23 35 324 168 144 48 64 128 256), losses := [] }

theorem u403 : Upper (D 1) (R 1) [22,33,320,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b403
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 23 35 324 168 144 96 90 154 282), lower := (rows 23 35 324 168 144 96 64 128 256), losses := [] }

theorem u404 : Upper (D 1) (R 1) [22,33,320,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b404
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 324 200 144 34 120 184 312), lower := (rows 23 35 324 200 144 34 64 128 256), losses := [] }

theorem u405 : Upper (D 1) (R 1) [22,33,320,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b405
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 23 35 324 200 144 40 114 178 306), lower := (rows 23 35 324 200 144 40 64 128 256), losses := [] }

theorem u406 : Upper (D 1) (R 1) [22,33,320,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b406
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 200 144 48 106 170 298), lower := (rows 23 35 324 200 144 48 64 128 256), losses := [] }

theorem u407 : Upper (D 1) (R 1) [22,33,320,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b407
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 266 144 48 224 224 480), lower := (rows 23 98 13 266 144 48 64 128 256), losses := [] }

theorem u408 : Upper (D 1) (R 1) [22,96,9,258,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b408
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 13 266 144 96 240 176 432), lower := (rows 23 98 13 266 144 96 64 128 256), losses := [] }

theorem u409 : Upper (D 1) (R 1) [22,96,9,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b409
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m410_16 : Upper (D 1) (R 1) [22,96,9,258,128,128,16] 13 :=
  permutation_upper _ _ _ [22,96,9,258,128,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8

theorem m410_32 : Upper (D 1) (R 1) [22,96,9,258,128,128,32] 13 :=
  permutation_upper _ _ _ [22,96,9,258,128,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9

def r410 : Route 9 := (fun mask => (mask,id))

def c410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u410 : Upper (D 1) (R 1) [22,96,9,258,128,128] 13 := by
  apply FastRouting.sound _ _ [22,96,9,258,128,128] 13 (by decide) (choices 1) [16,32] r410 c410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m410_16
  · exact m410_32

def b411 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 296 144 34 208 208 464), lower := (rows 23 98 13 296 144 34 64 128 256), losses := [] }

theorem u411 : Upper (D 1) (R 1) [22,96,9,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b411
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 13 296 144 48 194 194 450), lower := (rows 23 98 13 296 144 48 64 128 256), losses := [] }

theorem u412 : Upper (D 1) (R 1) [22,96,9,288,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b412
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 13 296 144 96 210 146 402), lower := (rows 23 98 13 296 144 96 64 128 256), losses := [] }

theorem u413 : Upper (D 1) (R 1) [22,96,9,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b413
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r414 : Route 9 := (fun mask => (mask,id))

def c414 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u414 : Upper (D 1) (R 1) [22,96,9,288,128,128] 13 := by
  apply FastRouting.sound _ _ [22,96,9,288,128,128] 13 (by decide) (choices 1) [2,16] r414 c414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u10
  · exact u11

def b415 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 23 98 261 138 144 40 112 240 368), lower := (rows 23 98 261 138 144 40 64 128 256), losses := [] }

theorem u415 : Upper (D 1) (R 1) [22,96,257,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b415
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 261 138 144 48 104 232 360), lower := (rows 23 98 261 138 144 48 64 128 256), losses := [] }

theorem u416 : Upper (D 1) (R 1) [22,96,257,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b416
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 261 138 144 96 120 184 312), lower := (rows 23 98 261 138 144 96 64 128 256), losses := [] }

theorem u417 : Upper (D 1) (R 1) [22,96,257,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b417
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 88, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 98 261 168 144 34 88 216 344), lower := (rows 23 98 261 168 144 34 64 128 256), losses := [] }

theorem u418 : Upper (D 1) (R 1) [22,96,257,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b418
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 23 98 261 168 144 40 82 210 338), lower := (rows 23 98 261 168 144 40 64 128 256), losses := [] }

theorem u419 : Upper (D 1) (R 1) [22,96,257,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b419
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P01
