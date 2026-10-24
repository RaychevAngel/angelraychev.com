import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0001

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 },{ cop := 5, region := 209, targets := 256 }], pairs := [(0,7),(0,8)], upper := (rows 113 7 14 392 144 288 112 240 368), lower := (rows 113 7 14 392 144 288 64 128 256), losses := [] }

theorem u360 : Upper (D 2) (R 2) [112,5,10,384,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b360
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 28 138 272 96 480 416 416), lower := (rows 113 7 28 138 272 96 64 128 256), losses := [] }

theorem u361 : Upper (D 2) (R 2) [112,5,24,130,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b361
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 488, targets := 16 },{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 7 28 138 272 160 352 480 352), lower := (rows 113 7 28 138 272 160 64 128 256), losses := [] }

theorem u362 : Upper (D 2) (R 2) [112,5,24,130,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b362
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 28 138 272 288 224 224 480), lower := (rows 113 7 28 138 272 288 64 128 256), losses := [] }

theorem u363 : Upper (D 2) (R 2) [112,5,24,130,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b363
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 168 272 34 448 448 448), lower := (rows 113 7 28 168 272 34 64 128 256), losses := [] }

theorem u364 : Upper (D 2) (R 2) [112,5,24,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b364
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 28 168 272 96 450 386 386), lower := (rows 113 7 28 168 272 96 64 128 256), losses := [] }

theorem u365 : Upper (D 2) (R 2) [112,5,24,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b365
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 7 28 168 272 160 322 450 322), lower := (rows 113 7 28 168 272 160 64 128 256), losses := [] }

theorem u366 : Upper (D 2) (R 2) [112,5,24,160,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b366
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 28 168 272 288 194 194 450), lower := (rows 113 7 28 168 272 288 64 128 256), losses := [] }

theorem u367 : Upper (D 2) (R 2) [112,5,24,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b367
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 390, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 134 152 272 40 352 480 352), lower := (rows 113 7 134 152 272 40 64 128 256), losses := [] }

theorem u368 : Upper (D 2) (R 2) [112,5,130,144,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b368
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 134 152 272 96 360 424 296), lower := (rows 113 7 134 152 272 96 64 128 256), losses := [] }

theorem u369 : Upper (D 2) (R 2) [112,5,130,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b369
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 134 152 272 288 104 232 360), lower := (rows 113 7 134 152 272 288 64 128 256), losses := [] }

theorem u370 : Upper (D 2) (R 2) [112,5,130,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b370
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 7 134 392 24 288 112 240 368), lower := (rows 113 7 134 392 24 288 64 128 256), losses := [] }

theorem u371 : Upper (D 2) (R 2) [112,5,130,384,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b371
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 134 392 48 288 88 216 344), lower := (rows 113 7 134 392 48 288 64 128 256), losses := [] }

theorem u372 : Upper (D 2) (R 2) [112,5,130,384,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b372
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 134 392 80 288 120 184 312), lower := (rows 113 7 134 392 80 288 64 128 256), losses := [] }

theorem u373 : Upper (D 2) (R 2) [112,5,130,384,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b373
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 140 26 272 96 480 416 416), lower := (rows 113 7 140 26 272 96 64 128 256), losses := [] }

theorem u374 : Upper (D 2) (R 2) [112,5,136,18,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b374
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 484, targets := 16 },{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7),(2,4)], upper := (rows 113 7 140 26 272 160 352 480 352), lower := (rows 113 7 140 26 272 160 64 128 256), losses := [] }

theorem u375 : Upper (D 2) (R 2) [112,5,136,18,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b375
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 140 26 272 288 224 224 480), lower := (rows 113 7 140 26 272 288 64 128 256), losses := [] }

theorem u376 : Upper (D 2) (R 2) [112,5,136,18,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b376
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 140 266 48 288 208 208 464), lower := (rows 113 7 140 266 48 288 64 128 256), losses := [] }

theorem u377 : Upper (D 2) (R 2) [112,5,136,258,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b377
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 140 266 80 288 240 176 432), lower := (rows 113 7 140 266 80 288 64 128 256), losses := [] }

theorem u378 : Upper (D 2) (R 2) [112,5,136,258,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b378
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 },{ cop := 5, region := 209, targets := 256 }], pairs := [(0,7),(0,8)], upper := (rows 113 7 140 266 144 288 112 240 368), lower := (rows 113 7 140 266 144 288 64 128 256), losses := [] }

theorem u379 : Upper (D 2) (R 2) [112,5,136,258,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b379
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 264, targets := 128 }], pairs := [(3,7)], upper := (rows 113 7 140 280 144 34 352 480 352), lower := (rows 113 7 140 280 144 34 64 128 256), losses := [] }

theorem u380 : Upper (D 2) (R 2) [112,5,136,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b380
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 140 280 144 96 354 418 290), lower := (rows 113 7 140 280 144 96 64 128 256), losses := [] }

theorem u381 : Upper (D 2) (R 2) [112,5,136,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b381
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m382_2 : Upper (D 2) (R 2) [112,5,136,272,128,256,2] 13 :=
  permutation_upper _ _ _ [112,5,136,272,128,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u61

theorem m382_32 : Upper (D 2) (R 2) [112,5,136,272,128,256,32] 13 :=
  permutation_upper _ _ _ [112,5,136,272,128,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u62

def r382 : Route 9 := (fun mask => (mask,id))

def c382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u382 : Upper (D 2) (R 2) [112,5,136,272,128,256] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,128,256] 13 (by decide) (choices 1) [2,32] r382 c382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m382_2
  · exact m382_32

def b383 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 168 272 34 328 456 328), lower := (rows 113 7 148 168 272 34 64 128 256), losses := [] }

theorem u383 : Upper (D 2) (R 2) [112,5,144,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b383
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 168 272 40 322 450 322), lower := (rows 113 7 148 168 272 40 64 128 256), losses := [] }

theorem u384 : Upper (D 2) (R 2) [112,5,144,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b384
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 148 168 272 96 330 394 266), lower := (rows 113 7 148 168 272 96 64 128 256), losses := [] }

theorem u385 : Upper (D 2) (R 2) [112,5,144,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b385
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 7 148 168 272 288 74 202 330), lower := (rows 113 7 148 168 272 288 64 128 256), losses := [] }

theorem u386 : Upper (D 2) (R 2) [112,5,144,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b386
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 7 148 266 272 40 224 224 480), lower := (rows 113 7 148 266 272 40 64 128 256), losses := [] }

theorem u387 : Upper (D 2) (R 2) [112,5,144,258,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b387
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 148 266 272 96 232 168 424), lower := (rows 113 7 148 266 272 96 64 128 256), losses := [] }

theorem u388 : Upper (D 2) (R 2) [112,5,144,258,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b388
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m389_8 : Upper (D 2) (R 2) [112,5,144,258,256,128,8] 13 :=
  permutation_upper _ _ _ [112,5,144,258,256,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u63

theorem m389_32 : Upper (D 2) (R 2) [112,5,144,258,256,128,32] 13 :=
  permutation_upper _ _ _ [112,5,144,258,256,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u64

def r389 : Route 9 := (fun mask => (mask,id))

def c389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u389 : Upper (D 2) (R 2) [112,5,144,258,256,128] 13 := by
  apply FastRouting.sound _ _ [112,5,144,258,256,128] 13 (by decide) (choices 1) [8,32] r389 c389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m389_8
  · exact m389_32

def b390 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 148 296 272 34 200 200 456), lower := (rows 113 7 148 296 272 34 64 128 256), losses := [] }

theorem u390 : Upper (D 2) (R 2) [112,5,144,288,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b390
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 148 296 272 40 194 194 450), lower := (rows 113 7 148 296 272 40 64 128 256), losses := [] }

theorem u391 : Upper (D 2) (R 2) [112,5,144,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b391
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 148 296 272 96 202 138 394), lower := (rows 113 7 148 296 272 96 64 128 256), losses := [] }

theorem u392 : Upper (D 2) (R 2) [112,5,144,288,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b392
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r393 : Route 9 := (fun mask => (mask,id))

def c393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u393 : Upper (D 2) (R 2) [112,5,144,288,256,128] 13 := by
  apply FastRouting.sound _ _ [112,5,144,288,256,128] 13 (by decide) (choices 1) [2,8] r393 c393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u65
  · exact u66

def b394 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 388 138 24 288 112 240 368), lower := (rows 113 7 388 138 24 288 64 128 256), losses := [] }

theorem u394 : Upper (D 2) (R 2) [112,5,384,130,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b394
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 7 388 138 48 288 88 216 344), lower := (rows 113 7 388 138 48 288 64 128 256), losses := [] }

theorem u395 : Upper (D 2) (R 2) [112,5,384,130,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b395
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 7 388 138 80 288 120 184 312), lower := (rows 113 7 388 138 80 288 64 128 256), losses := [] }

theorem u396 : Upper (D 2) (R 2) [112,5,384,130,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b396
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 22 137 272 96 480 416 416), lower := (rows 113 14 22 137 272 96 64 128 256), losses := [] }

theorem u397 : Upper (D 2) (R 2) [112,12,18,129,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b397
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 392, targets := 16 },{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 14 22 137 272 160 352 480 352), lower := (rows 113 14 22 137 272 160 64 128 256), losses := [] }

theorem u398 : Upper (D 2) (R 2) [112,12,18,129,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b398
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 14 22 137 272 288 224 224 480), lower := (rows 113 14 22 137 272 288 64 128 256), losses := [] }

theorem u399 : Upper (D 2) (R 2) [112,12,18,129,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b399
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 342, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 22 168 272 33 448 448 448), lower := (rows 113 14 22 168 272 33 64 128 256), losses := [] }

theorem u400 : Upper (D 2) (R 2) [112,12,18,160,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b400
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 22 168 272 96 449 385 385), lower := (rows 113 14 22 168 272 96 64 128 256), losses := [] }

theorem u401 : Upper (D 2) (R 2) [112,12,18,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b401
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 14 22 168 272 160 321 449 321), lower := (rows 113 14 22 168 272 160 64 128 256), losses := [] }

theorem u402 : Upper (D 2) (R 2) [112,12,18,160,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b402
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 14 22 168 272 288 193 193 449), lower := (rows 113 14 22 168 272 288 64 128 256), losses := [] }

theorem u403 : Upper (D 2) (R 2) [112,12,18,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b403
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 388, targets := 16 }], pairs := [(2,4)], upper := (rows 113 14 133 152 272 34 352 480 352), lower := (rows 113 14 133 152 272 34 64 128 256), losses := [] }

theorem u404 : Upper (D 2) (R 2) [112,12,129,144,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b404
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 133 152 272 96 354 418 290), lower := (rows 113 14 133 152 272 96 64 128 256), losses := [] }

theorem u405 : Upper (D 2) (R 2) [112,12,129,144,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b405
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 14 133 152 272 288 98 226 354), lower := (rows 113 14 133 152 272 288 64 128 256), losses := [] }

theorem u406 : Upper (D 2) (R 2) [112,12,129,144,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b406
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 388, targets := 16 }], pairs := [(2,4)], upper := (rows 113 14 133 280 144 34 352 480 352), lower := (rows 113 14 133 280 144 34 64 128 256), losses := [] }

theorem u407 : Upper (D 2) (R 2) [112,12,129,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b407
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 133 280 144 96 354 418 290), lower := (rows 113 14 133 280 144 96 64 128 256), losses := [] }

theorem u408 : Upper (D 2) (R 2) [112,12,129,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b408
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m409_2 : Upper (D 2) (R 2) [112,12,129,272,128,256,2] 13 :=
  permutation_upper _ _ _ [112,12,129,272,128,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u67

theorem m409_32 : Upper (D 2) (R 2) [112,12,129,272,128,256,32] 13 :=
  permutation_upper _ _ _ [112,12,129,272,128,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u68

def r409 : Route 9 := (fun mask => (mask,id))

def c409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u409 : Upper (D 2) (R 2) [112,12,129,272,128,256] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,128,256] 13 (by decide) (choices 1) [2,32] r409 c409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m409_2
  · exact m409_32

def b410 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 132, targets := 256 }], pairs := [(2,8)], upper := (rows 113 14 133 392 18 288 112 240 368), lower := (rows 113 14 133 392 18 288 64 128 256), losses := [] }

theorem u410 : Upper (D 2) (R 2) [112,12,129,384,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b410
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 14 133 392 48 288 82 210 338), lower := (rows 113 14 133 392 48 288 64 128 256), losses := [] }

theorem u411 : Upper (D 2) (R 2) [112,12,129,384,32,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b411
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 133 392 80 288 114 178 306), lower := (rows 113 14 133 392 80 288 64 128 256), losses := [] }

theorem u412 : Upper (D 2) (R 2) [112,12,129,384,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b412
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 148 168 17 288 322 450 322), lower := (rows 113 14 148 168 17 288 64 128 256), losses := [] }

theorem u413 : Upper (D 2) (R 2) [112,12,144,160,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b413
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 168 18 288 321 449 321), lower := (rows 113 14 148 168 18 288 64 128 256), losses := [] }

theorem u414 : Upper (D 2) (R 2) [112,12,144,160,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b414
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 148 168 80 288 323 387 259), lower := (rows 113 14 148 168 80 288 64 128 256), losses := [] }

theorem u415 : Upper (D 2) (R 2) [112,12,144,160,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b415
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 14 148 168 272 288 67 195 323), lower := (rows 113 14 148 168 272 288 64 128 256), losses := [] }

theorem u416 : Upper (D 2) (R 2) [112,12,144,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b416
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 362, targets := 16 }], pairs := [(1,4)], upper := (rows 113 14 148 296 17 160 322 450 322), lower := (rows 113 14 148 296 17 160 64 128 256), losses := [] }

theorem u417 : Upper (D 2) (R 2) [112,12,144,288,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b417
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 264, targets := 16 }], pairs := [(3,4)], upper := (rows 113 14 148 296 18 160 321 449 321), lower := (rows 113 14 148 296 18 160 64 128 256), losses := [] }

theorem u418 : Upper (D 2) (R 2) [112,12,144,288,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b418
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 14 148 296 80 160 323 387 259), lower := (rows 113 14 148 296 80 160 64 128 256), losses := [] }

theorem u419 : Upper (D 2) (R 2) [112,12,144,288,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b419
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P02
