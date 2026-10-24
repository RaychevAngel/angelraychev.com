import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0008
import IrregularNine14P09C0009

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 100 152 336 160 321 385 257), lower := (rows 7 42 100 152 336 160 64 128 256), losses := [] }

theorem u3360 : Upper (D 9) (R 9) [6,40,96,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3360 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 197, targets := 256 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,8),(2,0),(2,8),(3,5),(4,5)], upper := (rows 7 42 100 152 336 288 193 129 385), lower := (rows 7 42 100 152 336 288 64 128 256), losses := [] }

theorem u3361 : Upper (D 9) (R 9) [6,40,96,144,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3361 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3362 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 42 100 200 145 33 336 400 272), lower := (rows 7 42 100 200 145 33 64 128 256), losses := [] }

theorem u3362 : Upper (D 9) (R 9) [6,40,96,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3363 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 42 100 200 145 48 321 385 257), lower := (rows 7 42 100 200 145 48 64 128 256), losses := [] }

theorem u3363 : Upper (D 9) (R 9) [6,40,96,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3363 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3364 : Route 9 := (fun mask => (mask,id))

def c3364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3364 : Upper (D 9) (R 9) [6,40,96,192,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,129,256] 13 (by decide) (choices 1) [1,16,256] r3364 c3364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u482
  · exact u483
  · exact u484

def b3365 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 100 200 273 33 464 400 400), lower := (rows 7 42 100 200 273 33 64 128 256), losses := [] }

theorem u3365 : Upper (D 9) (R 9) [6,40,96,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3365 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3366 : Route 9 := (fun mask => (mask,id))

def c3366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3366 : Upper (D 9) (R 9) [6,40,96,192,257,16] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,257,16] 13 (by decide) (choices 1) [1,128,256] r3366 c3366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u485
  · exact u486
  · exact u487

def b3367 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 39, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(2,7),(4,7)], upper := (rows 7 42 100 200 273 160 337 401 273), lower := (rows 7 42 100 200 273 160 64 128 256), losses := [] }

theorem u3367 : Upper (D 9) (R 9) [6,40,96,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3367 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3368 : Route 9 := (fun mask => (mask,id))

def c3368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3368 : Upper (D 9) (R 9) [6,40,96,192,257,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,257,256] 13 (by decide) (choices 1) [1,16,128] r3368 c3368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u488
  · exact u489
  · exact u490

def b3369 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 42 100 200 400 33 337 401 273), lower := (rows 7 42 100 200 400 33 64 128 256), losses := [] }

theorem u3369 : Upper (D 9) (R 9) [6,40,96,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3369 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 200 400 48 321 385 257), lower := (rows 7 42 100 200 400 48 64 128 256), losses := [] }

theorem u3370 : Upper (D 9) (R 9) [6,40,96,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3370 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3371 : Route 9 := (fun mask => (mask,id))

def c3371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3371 : Upper (D 9) (R 9) [6,40,96,192,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,384,256] 13 (by decide) (choices 1) [1,16] r3371 c3371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u491
  · exact u492

def b3372 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 36, targets := 128 }], pairs := [(1,6),(2,7),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 392 81 33 464 400 400), lower := (rows 7 42 100 392 81 33 64 128 256), losses := [] }

theorem u3372 : Upper (D 9) (R 9) [6,40,96,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3372 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 42 100 392 81 48 449 385 385), lower := (rows 7 42 100 392 81 48 64 128 256), losses := [] }

theorem u3373 : Upper (D 9) (R 9) [6,40,96,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3373 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(2,7),(4,7)], upper := (rows 7 42 100 392 81 160 337 401 273), lower := (rows 7 42 100 392 81 160 64 128 256), losses := [] }

theorem u3374 : Upper (D 9) (R 9) [6,40,96,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3375 : Route 9 := (fun mask => (mask,id))

def c3375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3375 : Upper (D 9) (R 9) [6,40,96,384,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,129,1] 13 (by decide) (choices 1) [16,256] r3375 c3375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u493
  · exact u494

def b3376 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 392 145 48 321 449 321), lower := (rows 7 42 100 392 145 48 64 128 256), losses := [] }

theorem u3376 : Upper (D 9) (R 9) [6,40,96,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3376 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 42 100 392 145 96 337 401 273), lower := (rows 7 42 100 392 145 96 64 128 256), losses := [] }

theorem u3377 : Upper (D 9) (R 9) [6,40,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3377 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 100 392 145 288 81 209 337), lower := (rows 7 42 100 392 145 288 64 128 256), losses := [] }

theorem u3378 : Upper (D 9) (R 9) [6,40,96,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3378 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3379 : Route 9 := (fun mask => (mask,id))

def c3379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3379 : Upper (D 9) (R 9) [6,40,96,384,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192,1] 13 (by decide) (choices 1) [1,16,256] r3379 c3379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u495
  · exact u496
  · exact u497

def b3380 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 42 100 392 208 48 321 385 257), lower := (rows 7 42 100 392 208 48 64 128 256), losses := [] }

theorem u3380 : Upper (D 9) (R 9) [6,40,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3380 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 213, targets := 256 },{ cop := 3, region := 34, targets := 65 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,8)], upper := (rows 7 42 100 392 208 288 81 145 273), lower := (rows 7 42 100 392 208 288 64 128 256), losses := [] }

theorem u3381 : Upper (D 9) (R 9) [6,40,96,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3381 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3382 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 59, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 196 25 112 33 448 384 384), lower := (rows 7 42 196 25 112 33 64 128 256), losses := [] }

theorem u3382 : Upper (D 9) (R 9) [6,40,192,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3382 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3383 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 42 196 25 112 160 321 385 257), lower := (rows 7 42 196 25 112 160 64 128 256), losses := [] }

theorem u3383 : Upper (D 9) (R 9) [6,40,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3383 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3384 : Route 9 := (fun mask => (mask,id))

def c3384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3384 : Upper (D 9) (R 9) [6,40,192,17,96,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,96,256] 13 (by decide) (choices 1) [1,128,256] r3384 c3384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u498
  · exact u499
  · exact u500

def b3385 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 34, targets := 448 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 42 196 25 304 33 448 448 448), lower := (rows 7 42 196 25 304 33 64 128 256), losses := [] }

theorem u3385 : Upper (D 9) (R 9) [6,40,192,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3385 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3386 : Route 9 := (fun mask => (mask,id))

def c3386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3386 : Upper (D 9) (R 9) [6,40,192,17,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288,64] 13 (by decide) (choices 1) [1,128,256] r3386 c3386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u501
  · exact u502
  · exact u503

def b3387 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 196 25 304 288 193 193 449), lower := (rows 7 42 196 25 304 288 64 128 256), losses := [] }

theorem u3387 : Upper (D 9) (R 9) [6,40,192,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3387 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 384 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,0)], upper := (rows 7 42 196 25 336 33 480 416 416), lower := (rows 7 42 196 25 336 33 64 128 256), losses := [] }

theorem u3388 : Upper (D 9) (R 9) [6,40,192,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3388 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3389 : Route 9 := (fun mask => (mask,id))

def c3389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3389 : Upper (D 9) (R 9) [6,40,192,17,320,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320,128] 13 (by decide) (choices 1) [1,32,256] r3389 c3389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u504
  · exact u505
  · exact u506

def b3390 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 197, targets := 256 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,8),(1,0),(1,6),(1,7),(2,8)], upper := (rows 7 42 196 25 336 288 225 161 417), lower := (rows 7 42 196 25 336 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 304 64 128 256), good := (rows 6 42 196 58 368 288 64 128 288) },{ target := 7, region := (rows 1 10 4 8 16 304 64 0 256), good := (rows 7 42 68 59 368 288 64 0 288) }] }

theorem u3390 : Upper (D 9) (R 9) [6,40,192,17,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3390 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 42 196 73 176 33 336 400 272), lower := (rows 7 42 196 73 176 33 64 128 256), losses := [] }

theorem u3391 : Upper (D 9) (R 9) [6,40,192,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3391 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 42 196 73 176 48 321 385 257), lower := (rows 7 42 196 73 176 48 64 128 256), losses := [] }

theorem u3392 : Upper (D 9) (R 9) [6,40,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3392 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3393 : Route 9 := (fun mask => (mask,id))

def c3393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3393 : Upper (D 9) (R 9) [6,40,192,65,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,160,256] 13 (by decide) (choices 1) [1,16,256] r3393 c3393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u507
  · exact u508
  · exact u509

def r3394 : Route 9 := (fun mask => (mask,id))

def c3394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3394 : Upper (D 9) (R 9) [6,40,192,65,257,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,257,16] 13 (by decide) (choices 1) [32,128,256] r3394 c3394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u510
  · exact u511
  · exact u512

def b3395 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 3, region := 434, targets := 64 }], pairs := [(0,8),(1,6),(1,8),(3,8),(4,6)], upper := (rows 7 42 196 73 273 160 368 432 304), lower := (rows 7 42 196 73 273 160 64 128 256), losses := [] }

theorem u3395 : Upper (D 9) (R 9) [6,40,192,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3395 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3396 : Route 9 := (fun mask => (mask,id))

def c3396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3396 : Upper (D 9) (R 9) [6,40,192,65,257,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,257,256] 13 (by decide) (choices 1) [16,32,128] r3396 c3396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u513
  · exact u514
  · exact u515

def b3397 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 196 73 304 33 464 400 400), lower := (rows 7 42 196 73 304 33 64 128 256), losses := [] }

theorem u3397 : Upper (D 9) (R 9) [6,40,192,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3397 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3398 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 73 304 48 449 385 385), lower := (rows 7 42 196 73 304 48 64 128 256), losses := [] }

theorem u3398 : Upper (D 9) (R 9) [6,40,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3398 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 256 },{ cop := 3, region := 434, targets := 64 }], pairs := [(0,8),(1,6),(1,8),(3,8),(4,6)], upper := (rows 7 42 196 73 304 160 337 401 273), lower := (rows 7 42 196 73 304 160 64 128 256), losses := [] }

theorem u3399 : Upper (D 9) (R 9) [6,40,192,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3399 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 196 73 304 288 209 145 401), lower := (rows 7 42 196 73 304 288 64 128 256), losses := [] }

theorem u3400 : Upper (D 9) (R 9) [6,40,192,65,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3400 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 196 73 400 33 368 432 304), lower := (rows 7 42 196 73 400 33 64 128 256), losses := [] }

theorem u3401 : Upper (D 9) (R 9) [6,40,192,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3401 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3402 : Route 9 := (fun mask => (mask,id))

def c3402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3402 : Upper (D 9) (R 9) [6,40,192,65,384,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,384,16] 13 (by decide) (choices 1) [1,32,256] r3402 c3402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u516
  · exact u517
  · exact u518

def r3403 : Route 9 := (fun mask => (mask,id))

def c3403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3403 : Upper (D 9) (R 9) [6,40,192,65,384,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,384,256] 13 (by decide) (choices 1) [1,16,32] r3403 c3403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u519
  · exact u520
  · exact u521

def b3404 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,8),(1,7),(1,8),(3,8),(4,8)], upper := (rows 7 42 196 88 145 33 352 416 288), lower := (rows 7 42 196 88 145 33 64 128 256), losses := [] }

theorem u3404 : Upper (D 9) (R 9) [6,40,192,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3404 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3405 : Route 9 := (fun mask => (mask,id))

def c3405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3405 : Upper (D 9) (R 9) [6,40,192,80,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,129,256] 13 (by decide) (choices 1) [1,32,256] r3405 c3405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u522
  · exact u523
  · exact u524

def b3406 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 59, targets := 256 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,8),(1,8),(3,8),(4,8)], upper := (rows 7 42 196 88 176 33 321 385 257), lower := (rows 7 42 196 88 176 33 64 128 256), losses := [] }

theorem u3406 : Upper (D 9) (R 9) [6,40,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3406 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3407 : Route 9 := (fun mask => (mask,id))

def c3407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3407 : Upper (D 9) (R 9) [6,40,192,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,160,256] 13 (by decide) (choices 1) [1,256] r3407 c3407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u525
  · exact u526

def b3408 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(2,0),(4,6)], upper := (rows 7 42 196 88 273 33 480 416 416), lower := (rows 7 42 196 88 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 49 49 0 187 315), good := (rows 439 442 132 442 433 433 0 128 256) },{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 42 68 122 305 33 64 0 256) },{ target := 8, region := (rows 1 10 4 8 16 49 64 128 0), good := (rows 39 42 196 122 49 33 64 128 0) }] }

theorem u3408 : Upper (D 9) (R 9) [6,40,192,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3408 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3409 : Route 9 := (fun mask => (mask,id))

def c3409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3409 : Upper (D 9) (R 9) [6,40,192,80,257,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,257,128] 13 (by decide) (choices 1) [1,32,256] r3409 c3409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u527
  · exact u528
  · exact u529

def b3410 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 197, targets := 256 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,6)], upper := (rows 7 42 196 88 273 288 225 161 417), lower := (rows 7 42 196 88 273 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 304 64 128 256), good := (rows 6 42 196 122 304 288 64 128 288) },{ target := 6, region := (rows 1 10 4 8 17 313 0 145 273), good := (rows 439 42 132 442 433 288 0 128 288) }] }

theorem u3410 : Upper (D 9) (R 9) [6,40,192,80,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3410 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3411 : Route 9 := (fun mask => (mask,id))

def c3411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3411 : Upper (D 9) (R 9) [6,40,192,80,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288,1] 13 (by decide) (choices 1) [1,128,256] r3411 c3411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u530
  · exact u531
  · exact u532

def r3412 : Route 9 := (fun mask => (mask,id))

def c3412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3412 : Upper (D 9) (R 9) [6,40,192,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288,128] 13 (by decide) (choices 1) [1,256] r3412 c3412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u533
  · exact u534

def b3413 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 196 88 304 288 193 129 385), lower := (rows 7 42 196 88 304 288 64 128 256), losses := [] }

theorem u3413 : Upper (D 9) (R 9) [6,40,192,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3413 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3414 : Route 9 := (fun mask => (mask,id))

def c3414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3414 : Upper (D 9) (R 9) [6,40,192,80,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384,1] 13 (by decide) (choices 1) [1,32,256] r3414 c3414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u535
  · exact u536
  · exact u537

def b3415 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 256 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,8),(1,0),(1,6),(2,8),(4,6)], upper := (rows 7 42 196 88 400 288 97 161 289), lower := (rows 7 42 196 88 400 288 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 304 64 128 256), good := (rows 6 42 196 122 432 288 64 128 288) },{ target := 6, region := (rows 1 10 4 8 17 305 0 129 257), good := (rows 439 42 132 58 432 288 0 128 288) }] }

theorem u3415 : Upper (D 9) (R 9) [6,40,192,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3415 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3416 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 50, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(4,6)], upper := (rows 7 42 196 265 49 48 448 448 448), lower := (rows 7 42 196 265 49 48 64 128 256), losses := [] }

theorem u3416 : Upper (D 9) (R 9) [6,40,192,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3416 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3417 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 394, targets := 64 },{ cop := 4, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(2,5),(3,5),(3,6)], upper := (rows 7 42 196 265 49 96 464 400 400), lower := (rows 7 42 196 265 49 96 64 128 256), losses := [] }

theorem u3417 : Upper (D 9) (R 9) [6,40,192,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3417 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3418 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 192 },{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 42 196 265 49 288 208 208 464), lower := (rows 7 42 196 265 49 288 64 128 256), losses := [] }

theorem u3418 : Upper (D 9) (R 9) [6,40,192,257,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3418 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3419 : Route 9 := (fun mask => (mask,id))

def c3419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3419 : Upper (D 9) (R 9) [6,40,192,257,65,16] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65,16] 13 (by decide) (choices 1) [32,128,256] r3419 c3419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u538
  · exact u539
  · exact u540

#print axioms u3419
end Delivery.IrregularNine14.P09
