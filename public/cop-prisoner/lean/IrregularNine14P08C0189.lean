import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0057
import IrregularNine14P08C0058

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11340 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 265 81 176 240 176 432), lower := (rows 67 134 44 265 81 32 64 128 256), losses := [] }

theorem u11340 : Upper (D 8) (R 8) [66,132,40,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11341 : Route 9 := (fun mask => (mask,id))

def c11341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11341 : Upper (D 8) (R 8) [66,132,40,257,96] 13 := by
  apply FastRouting.sound _ _ [66,132,40,257,96] 13 (by decide) (choices 1) [1,16,128] r11341 c11341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3451
  · exact u3452
  · exact u3453

def b11342 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 44 265 145 112 112 240 368), lower := (rows 67 134 44 265 145 32 64 128 256), losses := [] }

theorem u11342 : Upper (D 8) (R 8) [66,132,40,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11343 : Route 9 := (fun mask => (mask,id))

def c11343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11343 : Upper (D 8) (R 8) [66,132,40,257,160] 13 := by
  apply FastRouting.sound _ _ [66,132,40,257,160] 13 (by decide) (choices 1) [1,16,64] r11343 c11343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3454
  · exact u3455
  · exact u3456

def r11344 : Route 9 := (fun mask => (mask,id))

def c11344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11344 : Upper (D 8) (R 8) [66,132,40,257,192] 13 := by
  apply FastRouting.sound _ _ [66,132,40,257,192] 13 (by decide) (choices 1) [1,16] r11344 c11344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3457
  · exact u3458

def r11345 : Route 9 := (fun mask => (mask,id))

def c11345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11345 : Upper (D 8) (R 8) [66,132,40,272,33] 13 := by
  apply FastRouting.sound _ _ [66,132,40,272,33] 13 (by decide) (choices 1) [1,64,128] r11345 c11345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3459
  · exact u3460
  · exact u3461

def b11346 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 280 81 161 225 161 417), lower := (rows 67 134 44 280 81 32 64 128 256), losses := [] }

theorem u11346 : Upper (D 8) (R 8) [66,132,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11347 : Route 9 := (fun mask => (mask,id))

def c11347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11347 : Upper (D 8) (R 8) [66,132,40,272,96] 13 := by
  apply FastRouting.sound _ _ [66,132,40,272,96] 13 (by decide) (choices 1) [1,128] r11347 c11347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3462
  · exact u3463

def b11348 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 44 280 145 97 97 225 353), lower := (rows 67 134 44 280 145 32 64 128 256), losses := [] }

theorem u11348 : Upper (D 8) (R 8) [66,132,40,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11349 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 280 176 97 97 225 353), lower := (rows 67 134 44 280 176 32 64 128 256), losses := [] }

theorem u11349 : Upper (D 8) (R 8) [66,132,40,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11350 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 44 280 208 33 97 161 289), lower := (rows 67 134 44 280 208 32 64 128 256), losses := [] }

theorem u11350 : Upper (D 8) (R 8) [66,132,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11351 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 261 25 56 224 224 224 480), lower := (rows 67 134 261 25 56 32 64 128 256), losses := [] }

theorem u11351 : Upper (D 8) (R 8) [66,132,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11352 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 261 25 88 160 224 160 416), lower := (rows 67 134 261 25 88 32 64 128 256), losses := [] }

theorem u11352 : Upper (D 8) (R 8) [66,132,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11353 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 25 112 168 232 168 424), lower := (rows 67 134 261 25 112 32 64 128 256), losses := [] }

theorem u11353 : Upper (D 8) (R 8) [66,132,257,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11354 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 261 25 152 96 96 224 352), lower := (rows 67 134 261 25 152 32 64 128 256), losses := [] }

theorem u11354 : Upper (D 8) (R 8) [66,132,257,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11355 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 25 176 104 104 232 360), lower := (rows 67 134 261 25 176 32 64 128 256), losses := [] }

theorem u11355 : Upper (D 8) (R 8) [66,132,257,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11356 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 25 208 40 104 168 296), lower := (rows 67 134 261 25 208 32 64 128 256), losses := [] }

theorem u11356 : Upper (D 8) (R 8) [66,132,257,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11357 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 261 41 56 240 240 240 496), lower := (rows 67 134 261 41 56 32 64 128 256), losses := [] }

theorem u11357 : Upper (D 8) (R 8) [66,132,257,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11358 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 41 88 176 240 176 432), lower := (rows 67 134 261 41 88 32 64 128 256), losses := [] }

theorem u11358 : Upper (D 8) (R 8) [66,132,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11359 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 41 112 184 248 184 440), lower := (rows 67 134 261 41 112 32 64 128 256), losses := [] }

theorem u11359 : Upper (D 8) (R 8) [66,132,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11360 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 41 152 112 112 240 368), lower := (rows 67 134 261 41 152 32 64 128 256), losses := [] }

theorem u11360 : Upper (D 8) (R 8) [66,132,257,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11361 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 41 176 120 120 248 376), lower := (rows 67 134 261 41 176 32 64 128 256), losses := [] }

theorem u11361 : Upper (D 8) (R 8) [66,132,257,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11362 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 67 134 261 41 208 56 120 184 312), lower := (rows 67 134 261 41 208 32 64 128 256), losses := [] }

theorem u11362 : Upper (D 8) (R 8) [66,132,257,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11362 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11363 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 56 56 225 225 225 481), lower := (rows 67 134 261 56 56 32 64 128 256), losses := [] }

theorem u11363 : Upper (D 8) (R 8) [66,132,257,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11364 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 56 81 168 232 168 424), lower := (rows 67 134 261 56 81 32 64 128 256), losses := [] }

theorem u11364 : Upper (D 8) (R 8) [66,132,257,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11365 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 56 88 161 225 161 417), lower := (rows 67 134 261 56 88 32 64 128 256), losses := [] }

theorem u11365 : Upper (D 8) (R 8) [66,132,257,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11365 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11366 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 56 112 169 233 169 425), lower := (rows 67 134 261 56 112 32 64 128 256), losses := [] }

theorem u11366 : Upper (D 8) (R 8) [66,132,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11367 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 261 56 145 104 104 232 360), lower := (rows 67 134 261 56 145 32 64 128 256), losses := [] }

theorem u11367 : Upper (D 8) (R 8) [66,132,257,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11368 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 261 56 152 97 97 225 353), lower := (rows 67 134 261 56 152 32 64 128 256), losses := [] }

theorem u11368 : Upper (D 8) (R 8) [66,132,257,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11369 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 56 176 105 105 233 361), lower := (rows 67 134 261 56 176 32 64 128 256), losses := [] }

theorem u11369 : Upper (D 8) (R 8) [66,132,257,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11370 : Route 9 := (fun mask => (mask,id))

def c11370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11370 : Upper (D 8) (R 8) [66,132,257,48,192] 13 := by
  apply FastRouting.sound _ _ [66,132,257,48,192] 13 (by decide) (choices 1) [1,8] r11370 c11370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3464
  · exact u3465

def b11371 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 73 152 48 112 176 304), lower := (rows 67 134 261 73 152 32 64 128 256), losses := [] }

theorem u11371 : Upper (D 8) (R 8) [66,132,257,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11372 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 73 176 56 120 184 312), lower := (rows 67 134 261 73 176 32 64 128 256), losses := [] }

theorem u11372 : Upper (D 8) (R 8) [66,132,257,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11373 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 261 88 145 40 104 168 296), lower := (rows 67 134 261 88 145 32 64 128 256), losses := [] }

theorem u11373 : Upper (D 8) (R 8) [66,132,257,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11373 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11374 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 261 88 152 33 97 161 289), lower := (rows 67 134 261 88 152 32 64 128 256), losses := [] }

theorem u11374 : Upper (D 8) (R 8) [66,132,257,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11375 : Route 9 := (fun mask => (mask,id))

def c11375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11375 : Upper (D 8) (R 8) [66,132,257,80,160] 13 := by
  apply FastRouting.sound _ _ [66,132,257,80,160] 13 (by decide) (choices 1) [1,8] r11375 c11375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3466
  · exact u3467

def b11376 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 261 104 145 56 120 184 312), lower := (rows 67 134 261 104 145 32 64 128 256), losses := [] }

theorem u11376 : Upper (D 8) (R 8) [66,132,257,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11377 : Route 9 := (fun mask => (mask,id))

def c11377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11377 : Upper (D 8) (R 8) [66,132,257,96,136] 13 := by
  apply FastRouting.sound _ _ [66,132,257,96,136] 13 (by decide) (choices 1) [1,16] r11377 c11377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3468
  · exact u3469

def r11378 : Route 9 := (fun mask => (mask,id))

def c11378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11378 : Upper (D 8) (R 8) [66,132,257,96,160] 13 := by
  apply FastRouting.sound _ _ [66,132,257,96,160] 13 (by decide) (choices 1) [1,8,16] r11378 c11378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3470
  · exact u3471
  · exact u3472

def b11379 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 268 25 49 224 224 224 480), lower := (rows 67 134 268 25 49 32 64 128 256), losses := [] }

theorem u11379 : Upper (D 8) (R 8) [66,132,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11380 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 268 25 81 160 224 160 416), lower := (rows 67 134 268 25 81 32 64 128 256), losses := [] }

theorem u11380 : Upper (D 8) (R 8) [66,132,264,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11381 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 25 112 161 225 161 417), lower := (rows 67 134 268 25 112 32 64 128 256), losses := [] }

theorem u11381 : Upper (D 8) (R 8) [66,132,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11382 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 268 25 145 96 96 224 352), lower := (rows 67 134 268 25 145 32 64 128 256), losses := [] }

theorem u11382 : Upper (D 8) (R 8) [66,132,264,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11383 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 268 25 176 97 97 225 353), lower := (rows 67 134 268 25 176 32 64 128 256), losses := [] }

theorem u11383 : Upper (D 8) (R 8) [66,132,264,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11384 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 25 208 33 97 161 289), lower := (rows 67 134 268 25 208 32 64 128 256), losses := [] }

theorem u11384 : Upper (D 8) (R 8) [66,132,264,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11384 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11385 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 134 268 41 49 240 240 240 496), lower := (rows 67 134 268 41 49 32 64 128 256), losses := [] }

theorem u11385 : Upper (D 8) (R 8) [66,132,264,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11386 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 41 81 176 240 176 432), lower := (rows 67 134 268 41 81 32 64 128 256), losses := [] }

theorem u11386 : Upper (D 8) (R 8) [66,132,264,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11387 : Route 9 := (fun mask => (mask,id))

def c11387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11387 : Upper (D 8) (R 8) [66,132,264,33,96] 13 := by
  apply FastRouting.sound _ _ [66,132,264,33,96] 13 (by decide) (choices 1) [1,16,128] r11387 c11387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3473
  · exact u3474
  · exact u3475

def b11388 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 268 41 145 112 112 240 368), lower := (rows 67 134 268 41 145 32 64 128 256), losses := [] }

theorem u11388 : Upper (D 8) (R 8) [66,132,264,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11389 : Route 9 := (fun mask => (mask,id))

def c11389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11389 : Upper (D 8) (R 8) [66,132,264,33,160] 13 := by
  apply FastRouting.sound _ _ [66,132,264,33,160] 13 (by decide) (choices 1) [1,16,64] r11389 c11389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3476
  · exact u3477
  · exact u3478

def r11390 : Route 9 := (fun mask => (mask,id))

def c11390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11390 : Upper (D 8) (R 8) [66,132,264,33,192] 13 := by
  apply FastRouting.sound _ _ [66,132,264,33,192] 13 (by decide) (choices 1) [1,16] r11390 c11390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3479
  · exact u3480

def b11391 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 268 56 49 225 225 225 481), lower := (rows 67 134 268 56 49 32 64 128 256), losses := [] }

theorem u11391 : Upper (D 8) (R 8) [66,132,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11392 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 56 81 161 225 161 417), lower := (rows 67 134 268 56 81 32 64 128 256), losses := [] }

theorem u11392 : Upper (D 8) (R 8) [66,132,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11393 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 268 56 112 161 225 161 417), lower := (rows 67 134 268 56 112 32 64 128 256), losses := [] }

theorem u11393 : Upper (D 8) (R 8) [66,132,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11394 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 268 56 145 97 97 225 353), lower := (rows 67 134 268 56 145 32 64 128 256), losses := [] }

theorem u11394 : Upper (D 8) (R 8) [66,132,264,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11395 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 268 56 176 97 97 225 353), lower := (rows 67 134 268 56 176 32 64 128 256), losses := [] }

theorem u11395 : Upper (D 8) (R 8) [66,132,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11396 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 134 268 56 208 33 97 161 289), lower := (rows 67 134 268 56 208 32 64 128 256), losses := [] }

theorem u11396 : Upper (D 8) (R 8) [66,132,264,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11397 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 292 25 25 224 224 224 480), lower := (rows 67 134 292 25 25 32 64 128 256), losses := [] }

theorem u11397 : Upper (D 8) (R 8) [66,132,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11398 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 67 134 292 25 49 232 232 232 488), lower := (rows 67 134 292 25 49 32 64 128 256), losses := [] }

theorem u11398 : Upper (D 8) (R 8) [66,132,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11399 : Route 9 := (fun mask => (mask,id))

def c11399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11399 : Upper (D 8) (R 8) [66,132,288,17,40] 13 := by
  apply FastRouting.sound _ _ [66,132,288,17,40] 13 (by decide) (choices 1) [1,64,128] r11399 c11399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3481
  · exact u3482
  · exact u3483

#print axioms u11399
end Delivery.IrregularNine14.P08
