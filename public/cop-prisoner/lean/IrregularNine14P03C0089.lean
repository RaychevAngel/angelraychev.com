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

def b5340 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 25 112 225 193 193 449), lower := (rows 289 7 14 25 112 32 64 128 256), losses := [] }

theorem u5340 : Upper (D 3) (R 3) [288,5,10,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5340
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5341 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 25 208 225 225 225 481), lower := (rows 289 7 14 25 208 32 64 128 256), losses := [] }

theorem u5341 : Upper (D 3) (R 3) [288,5,10,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5341
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5342 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 41 81 240 208 208 464), lower := (rows 289 7 14 41 81 32 64 128 256), losses := [] }

theorem u5342 : Upper (D 3) (R 3) [288,5,10,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5342
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5343 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 41 208 241 209 209 465), lower := (rows 289 7 14 41 208 32 64 128 256), losses := [] }

theorem u5343 : Upper (D 3) (R 3) [288,5,10,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5343
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 56 81 225 193 193 449), lower := (rows 289 7 14 56 81 32 64 128 256), losses := [] }

theorem u5344 : Upper (D 3) (R 3) [288,5,10,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5344
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5345 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 56 208 225 193 193 449), lower := (rows 289 7 14 56 208 32 64 128 256), losses := [] }

theorem u5345 : Upper (D 3) (R 3) [288,5,10,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5345
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5346 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 81 176 240 176 432), lower := (rows 289 7 14 73 81 32 64 128 256), losses := [] }

theorem u5346 : Upper (D 3) (R 3) [288,5,10,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5347 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 112 177 209 145 401), lower := (rows 289 7 14 73 112 32 64 128 256), losses := [] }

theorem u5347 : Upper (D 3) (R 3) [288,5,10,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5347
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5348 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 145 240 240 240 496), lower := (rows 289 7 14 73 145 32 64 128 256), losses := [] }

theorem u5348 : Upper (D 3) (R 3) [288,5,10,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5348
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 176 241 209 209 465), lower := (rows 289 7 14 73 176 32 64 128 256), losses := [] }

theorem u5349 : Upper (D 3) (R 3) [288,5,10,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5349
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5350 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 208 177 241 177 433), lower := (rows 289 7 14 73 208 32 64 128 256), losses := [] }

theorem u5350 : Upper (D 3) (R 3) [288,5,10,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5350
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5351 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 88 49 225 193 193 449), lower := (rows 289 7 14 88 49 32 64 128 256), losses := [] }

theorem u5351 : Upper (D 3) (R 3) [288,5,10,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5351
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5352 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 88 81 161 225 161 417), lower := (rows 289 7 14 88 81 32 64 128 256), losses := [] }

theorem u5352 : Upper (D 3) (R 3) [288,5,10,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5352
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5353 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 112 161 193 129 385), lower := (rows 289 7 14 88 112 32 64 128 256), losses := [] }

theorem u5353 : Upper (D 3) (R 3) [288,5,10,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5353
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5354 : Route 9 := (fun mask => (mask,id))

def c5354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5354 : Upper (D 3) (R 3) [288,5,10,80,129] 13 := by
  apply FastRouting.sound _ _ [288,5,10,80,129] 13 (by decide) (choices 1) [1,64,128] r5354 c5354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2077
  · exact u2078
  · exact u2079

def r5355 : Route 9 := (fun mask => (mask,id))

def c5355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5355 : Upper (D 3) (R 3) [288,5,10,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,10,80,160] 13 (by decide) (choices 1) [1,64,128] r5355 c5355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2080
  · exact u2081
  · exact u2082

def b5356 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 208 161 225 161 417), lower := (rows 289 7 14 88 208 32 64 128 256), losses := [] }

theorem u5356 : Upper (D 3) (R 3) [288,5,10,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5356
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5357 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 104 81 177 209 145 401), lower := (rows 289 7 14 104 81 32 64 128 256), losses := [] }

theorem u5357 : Upper (D 3) (R 3) [288,5,10,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5358 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 104 145 241 209 209 465), lower := (rows 289 7 14 104 145 32 64 128 256), losses := [] }

theorem u5358 : Upper (D 3) (R 3) [288,5,10,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5358
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5359 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 104 208 177 209 145 401), lower := (rows 289 7 14 104 208 32 64 128 256), losses := [] }

theorem u5359 : Upper (D 3) (R 3) [288,5,10,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5359
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5360 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 200 49 241 209 209 465), lower := (rows 289 7 14 200 49 32 64 128 256), losses := [] }

theorem u5360 : Upper (D 3) (R 3) [288,5,10,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5360
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5361 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 200 81 177 241 177 433), lower := (rows 289 7 14 200 81 32 64 128 256), losses := [] }

theorem u5361 : Upper (D 3) (R 3) [288,5,10,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5361
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5362 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 200 112 177 209 145 401), lower := (rows 289 7 14 200 112 32 64 128 256), losses := [] }

theorem u5362 : Upper (D 3) (R 3) [288,5,10,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5362
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5363 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 7 14 200 208 49 113 177 305), lower := (rows 289 7 14 200 208 32 64 128 256), losses := [] }

theorem u5363 : Upper (D 3) (R 3) [288,5,10,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5363
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5364 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 41 81 226 194 194 450), lower := (rows 289 7 28 41 81 32 64 128 256), losses := [] }

theorem u5364 : Upper (D 3) (R 3) [288,5,24,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5365 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 41 82 225 193 193 449), lower := (rows 289 7 28 41 82 32 64 128 256), losses := [] }

theorem u5365 : Upper (D 3) (R 3) [288,5,24,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5366 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 41 208 227 195 195 451), lower := (rows 289 7 28 41 208 32 64 128 256), losses := [] }

theorem u5366 : Upper (D 3) (R 3) [288,5,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5366
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5367 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 28 42 81 225 193 193 449), lower := (rows 289 7 28 42 81 32 64 128 256), losses := [] }

theorem u5367 : Upper (D 3) (R 3) [288,5,24,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5368 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 28 42 208 225 193 193 449), lower := (rows 289 7 28 42 208 32 64 128 256), losses := [] }

theorem u5368 : Upper (D 3) (R 3) [288,5,24,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5369 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 73 81 162 226 162 418), lower := (rows 289 7 28 73 81 32 64 128 256), losses := [] }

theorem u5369 : Upper (D 3) (R 3) [288,5,24,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5369
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5370 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 73 82 161 225 161 417), lower := (rows 289 7 28 73 82 32 64 128 256), losses := [] }

theorem u5370 : Upper (D 3) (R 3) [288,5,24,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5370
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5371 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 73 112 163 195 131 387), lower := (rows 289 7 28 73 112 32 64 128 256), losses := [] }

theorem u5371 : Upper (D 3) (R 3) [288,5,24,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5371
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m5372_128 : Upper (D 3) (R 3) [288,5,24,65,129,128] 13 :=
  permutation_upper _ _ _ [288,5,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2084

def r5372 : Route 9 := (fun mask => (mask,id))

def c5372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5372 : Upper (D 3) (R 3) [288,5,24,65,129] 13 := by
  apply FastRouting.sound _ _ [288,5,24,65,129] 13 (by decide) (choices 1) [2,64,128] r5372 c5372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2083
  · exact u2084
  · exact m5372_128

def r5373 : Route 9 := (fun mask => (mask,id))

def c5373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5373 : Upper (D 3) (R 3) [288,5,24,65,130] 13 := by
  apply FastRouting.sound _ _ [288,5,24,65,130] 13 (by decide) (choices 1) [1,64,128] r5373 c5373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2085
  · exact u2086
  · exact u2087

def b5374 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 28 73 176 227 195 195 451), lower := (rows 289 7 28 73 176 32 64 128 256), losses := [] }

theorem u5374 : Upper (D 3) (R 3) [288,5,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5374
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 73 208 163 227 163 419), lower := (rows 289 7 28 73 208 32 64 128 256), losses := [] }

theorem u5375 : Upper (D 3) (R 3) [288,5,24,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5375
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5376 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 74 112 161 193 129 385), lower := (rows 289 7 28 74 112 32 64 128 256), losses := [] }

theorem u5376 : Upper (D 3) (R 3) [288,5,24,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5376
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5377 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 28 74 176 225 193 193 449), lower := (rows 289 7 28 74 176 32 64 128 256), losses := [] }

theorem u5377 : Upper (D 3) (R 3) [288,5,24,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5377
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5378 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 74 208 161 225 161 417), lower := (rows 289 7 28 74 208 32 64 128 256), losses := [] }

theorem u5378 : Upper (D 3) (R 3) [288,5,24,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5378
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5379 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 104 208 163 195 131 387), lower := (rows 289 7 28 104 208 32 64 128 256), losses := [] }

theorem u5379 : Upper (D 3) (R 3) [288,5,24,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5379
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5380 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 289 7 28 200 208 35 99 163 291), lower := (rows 289 7 28 200 208 32 64 128 256), losses := [] }

theorem u5380 : Upper (D 3) (R 3) [288,5,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5380
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5381 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 25 82 232 200 200 456), lower := (rows 289 7 37 25 82 32 64 128 256), losses := [] }

theorem u5381 : Upper (D 3) (R 3) [288,5,33,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5381
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 25 88 226 194 194 450), lower := (rows 289 7 37 25 88 32 64 128 256), losses := [] }

theorem u5382 : Upper (D 3) (R 3) [288,5,33,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5382
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 25 208 234 202 202 458), lower := (rows 289 7 37 25 208 32 64 128 256), losses := [] }

theorem u5383 : Upper (D 3) (R 3) [288,5,33,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5383
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5384 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 81 232 200 200 456), lower := (rows 289 7 37 26 81 32 64 128 256), losses := [] }

theorem u5384 : Upper (D 3) (R 3) [288,5,33,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5384
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5385 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 88 225 193 193 449), lower := (rows 289 7 37 26 88 32 64 128 256), losses := [] }

theorem u5385 : Upper (D 3) (R 3) [288,5,33,18,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5385
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 208 233 201 201 457), lower := (rows 289 7 37 26 208 32 64 128 256), losses := [] }

theorem u5386 : Upper (D 3) (R 3) [288,5,33,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5386
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5387 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 73 82 184 216 152 408), lower := (rows 289 7 37 73 82 32 64 128 256), losses := [] }

theorem u5387 : Upper (D 3) (R 3) [288,5,33,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5387
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5388 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 73 146 248 216 216 472), lower := (rows 289 7 37 73 146 32 64 128 256), losses := [] }

theorem u5388 : Upper (D 3) (R 3) [288,5,33,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5388
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5389 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 73 152 242 210 210 466), lower := (rows 289 7 37 73 152 32 64 128 256), losses := [] }

theorem u5389 : Upper (D 3) (R 3) [288,5,33,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5389
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5390 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 73 208 186 218 154 410), lower := (rows 289 7 37 73 208 32 64 128 256), losses := [] }

theorem u5390 : Upper (D 3) (R 3) [288,5,33,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5390
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5391 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 152 241 209 209 465), lower := (rows 289 7 37 74 152 32 64 128 256), losses := [] }

theorem u5391 : Upper (D 3) (R 3) [288,5,33,66,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5391
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5392 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 208 185 217 153 409), lower := (rows 289 7 37 74 208 32 64 128 256), losses := [] }

theorem u5392 : Upper (D 3) (R 3) [288,5,33,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5392
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 88 152 227 195 195 451), lower := (rows 289 7 37 88 152 32 64 128 256), losses := [] }

theorem u5393 : Upper (D 3) (R 3) [288,5,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5393
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 25 88 225 193 193 449), lower := (rows 289 7 38 25 88 32 64 128 256), losses := [] }

theorem u5394 : Upper (D 3) (R 3) [288,5,34,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5394
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 25 208 233 201 201 457), lower := (rows 289 7 38 25 208 32 64 128 256), losses := [] }

theorem u5395 : Upper (D 3) (R 3) [288,5,34,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5395
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5396 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 145 248 216 216 472), lower := (rows 289 7 38 73 145 32 64 128 256), losses := [] }

theorem u5396 : Upper (D 3) (R 3) [288,5,34,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5396
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5397 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 152 241 209 209 465), lower := (rows 289 7 38 73 152 32 64 128 256), losses := [] }

theorem u5397 : Upper (D 3) (R 3) [288,5,34,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5397
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5398 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 208 185 217 153 409), lower := (rows 289 7 38 73 208 32 64 128 256), losses := [] }

theorem u5398 : Upper (D 3) (R 3) [288,5,34,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5398
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5399 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 88 152 225 193 193 449), lower := (rows 289 7 38 88 152 32 64 128 256), losses := [] }

theorem u5399 : Upper (D 3) (R 3) [288,5,34,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5399
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P03
