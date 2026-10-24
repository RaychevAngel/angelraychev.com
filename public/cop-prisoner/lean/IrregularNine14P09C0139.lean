import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0099
import IrregularNine14P09C0100

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8340 : Route 9 := (fun mask => (mask,id))

def c8340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8340 : Upper (D 9) (R 9) [96,5,384,129,264] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,264] 13 (by decide) (choices 1) [2,16,64] r8340 c8340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5969
  · exact u5970
  · exact u5971

def r8341 : Route 9 := (fun mask => (mask,id))

def c8341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8341 : Upper (D 9) (R 9) [96,5,384,129,288] 13 := by
  apply FastRouting.sound _ _ [96,5,384,129,288] 13 (by decide) (choices 1) [2,8,16,64] r8341 c8341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5972
  · exact u5973
  · exact u5974
  · exact u5975

def r8342 : Route 9 := (fun mask => (mask,id))

def c8342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8342 : Upper (D 9) (R 9) [96,5,384,130,264] 13 := by
  apply FastRouting.sound _ _ [96,5,384,130,264] 13 (by decide) (choices 1) [1,16,64] r8342 c8342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5976
  · exact u5977
  · exact u5978

def r8343 : Route 9 := (fun mask => (mask,id))

def c8343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8343 : Upper (D 9) (R 9) [96,5,384,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,384,130,288] 13 (by decide) (choices 1) [1,8,16,64] r8343 c8343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5979
  · exact u5980
  · exact u5981
  · exact u5982

def b8344 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6),(4,0),(4,5)], upper := (rows 97 7 388 152 280 99 99 227 355), lower := (rows 97 7 388 152 280 32 64 128 256), losses := [] }

theorem u8344 : Upper (D 9) (R 9) [96,5,384,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8344 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8345 : Route 9 := (fun mask => (mask,id))

def c8345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8345 : Upper (D 9) (R 9) [96,5,384,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,384,144,288] 13 (by decide) (choices 1) [1,2,8,64] r8345 c8345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5983
  · exact u5984
  · exact u5985
  · exact u5986

def r8346 : Route 9 := (fun mask => (mask,id))

def c8346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8346 : Upper (D 9) (R 9) [96,5,384,160,320] 13 := by
  apply FastRouting.sound _ _ [96,5,384,160,320] 13 (by decide) (choices 1) [1,2,8,16] r8346 c8346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5987
  · exact u5988
  · exact u5989
  · exact u5990

def b8347 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 14 22 41 145 480 448 448 448), lower := (rows 97 14 22 41 145 32 64 128 256), losses := [] }

theorem u8347 : Upper (D 9) (R 9) [96,12,18,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8347 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8348 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 97 14 22 41 208 417 449 385 385), lower := (rows 97 14 22 41 208 32 64 128 256), losses := [] }

theorem u8348 : Upper (D 9) (R 9) [96,12,18,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8348 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8349 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 14 22 41 400 481 449 449 449), lower := (rows 97 14 22 41 400 32 64 128 256), losses := [] }

theorem u8349 : Upper (D 9) (R 9) [96,12,18,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8349 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8350 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 14 22 104 145 417 449 385 385), lower := (rows 97 14 22 104 145 32 64 128 256), losses := [] }

theorem u8350 : Upper (D 9) (R 9) [96,12,18,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8350 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8351 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 14 22 104 400 417 449 385 385), lower := (rows 97 14 22 104 400 32 64 128 256), losses := [] }

theorem u8351 : Upper (D 9) (R 9) [96,12,18,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8351 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8352 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 22, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(2,5),(2,6)], upper := (rows 97 14 22 137 145 352 352 480 352), lower := (rows 97 14 22 137 145 32 64 128 256), losses := [] }

theorem u8352 : Upper (D 9) (R 9) [96,12,18,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8352 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8353 : Route 9 := (fun mask => (mask,id))

def c8353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8353 : Upper (D 9) (R 9) [96,12,18,129,160] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,160] 13 (by decide) (choices 1) [1,64,256] r8353 c8353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5991
  · exact u5992
  · exact u5993

theorem m8354_256 : Upper (D 9) (R 9) [96,12,18,129,257,256] 13 :=
  permutation_upper _ _ _ [96,12,18,129,257,128] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5995

def r8354 : Route 9 := (fun mask => (mask,id))

def c8354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8354 : Upper (D 9) (R 9) [96,12,18,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,257] 13 (by decide) (choices 1) [64,128,256] r8354 c8354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5994
  · exact u5995
  · exact m8354_256

def r8355 : Route 9 := (fun mask => (mask,id))

def c8355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8355 : Upper (D 9) (R 9) [96,12,18,129,288] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,288] 13 (by decide) (choices 1) [1,64,128,256] r8355 c8355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5996
  · exact u5997
  · exact u5998
  · exact u5999

def r8356 : Route 9 := (fun mask => (mask,id))

def c8356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8356 : Upper (D 9) (R 9) [96,12,18,129,384] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129,384] 13 (by decide) (choices 1) [1,64,256] r8356 c8356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6000
  · exact u6001
  · exact u6002

def r8357 : Route 9 := (fun mask => (mask,id))

def c8357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8357 : Upper (D 9) (R 9) [96,12,18,160,192] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160,192] 13 (by decide) (choices 1) [1,256] r8357 c8357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6003
  · exact u6004

def r8358 : Route 9 := (fun mask => (mask,id))

def c8358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8358 : Upper (D 9) (R 9) [96,12,18,160,320] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160,320] 13 (by decide) (choices 1) [1,128,256] r8358 c8358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6005
  · exact u6006
  · exact u6007

def r8359 : Route 9 := (fun mask => (mask,id))

def c8359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8359 : Upper (D 9) (R 9) [96,12,18,160,384] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160,384] 13 (by decide) (choices 1) [1,64,256] r8359 c8359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6008
  · exact u6009
  · exact u6010

def b8360 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 22, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(2,0),(2,5)], upper := (rows 97 14 22 392 400 97 97 225 353), lower := (rows 97 14 22 392 400 32 64 128 256), losses := [] }

theorem u8360 : Upper (D 9) (R 9) [96,12,18,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8360 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8361 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 14 37 74 145 432 464 400 400), lower := (rows 97 14 37 74 145 32 64 128 256), losses := [] }

theorem u8361 : Upper (D 9) (R 9) [96,12,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8361 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8362 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 14 37 74 400 433 465 401 401), lower := (rows 97 14 37 74 400 32 64 128 256), losses := [] }

theorem u8362 : Upper (D 9) (R 9) [96,12,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8363 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 88 145 418 450 386 386), lower := (rows 97 14 37 88 145 32 64 128 256), losses := [] }

theorem u8363 : Upper (D 9) (R 9) [96,12,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8363 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8364 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 97 14 37 88 146 417 449 385 385), lower := (rows 97 14 37 88 146 32 64 128 256), losses := [] }

theorem u8364 : Upper (D 9) (R 9) [96,12,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8364 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8365 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 88 400 419 451 387 387), lower := (rows 97 14 37 88 400 32 64 128 256), losses := [] }

theorem u8365 : Upper (D 9) (R 9) [96,12,33,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8365 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8366 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 137 82 432 464 400 400), lower := (rows 97 14 37 137 82 32 64 128 256), losses := [] }

theorem u8366 : Upper (D 9) (R 9) [96,12,33,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8366 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8367 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 137 146 368 336 464 336), lower := (rows 97 14 37 137 146 32 64 128 256), losses := [] }

theorem u8367 : Upper (D 9) (R 9) [96,12,33,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8367 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8368 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 137 208 306 338 402 274), lower := (rows 97 14 37 137 208 32 64 128 256), losses := [] }

theorem u8368 : Upper (D 9) (R 9) [96,12,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8368 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8369 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 137 274 496 464 464 464), lower := (rows 97 14 37 137 274 32 64 128 256), losses := [] }

theorem u8369 : Upper (D 9) (R 9) [96,12,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8369 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8370 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 137 336 434 466 402 402), lower := (rows 97 14 37 137 336 32 64 128 256), losses := [] }

theorem u8370 : Upper (D 9) (R 9) [96,12,33,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8370 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8371 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 137 400 370 338 466 338), lower := (rows 97 14 37 137 400 32 64 128 256), losses := [] }

theorem u8371 : Upper (D 9) (R 9) [96,12,33,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8371 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8372 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 138 145 368 336 464 336), lower := (rows 97 14 37 138 145 32 64 128 256), losses := [] }

theorem u8372 : Upper (D 9) (R 9) [96,12,33,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8372 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8373 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 138 208 305 337 401 273), lower := (rows 97 14 37 138 208 32 64 128 256), losses := [] }

theorem u8373 : Upper (D 9) (R 9) [96,12,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8373 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8374 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 138 273 496 464 464 464), lower := (rows 97 14 37 138 273 32 64 128 256), losses := [] }

theorem u8374 : Upper (D 9) (R 9) [96,12,33,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8375 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 138 336 433 465 401 401), lower := (rows 97 14 37 138 336 32 64 128 256), losses := [] }

theorem u8375 : Upper (D 9) (R 9) [96,12,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8375 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8376 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 138 400 369 337 465 337), lower := (rows 97 14 37 138 400 32 64 128 256), losses := [] }

theorem u8376 : Upper (D 9) (R 9) [96,12,33,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8376 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8377 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 474, targets := 32 },{ cop := 0, region := 4, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 97 14 37 152 82 417 449 385 385), lower := (rows 97 14 37 152 82 32 64 128 256), losses := [] }

theorem u8377 : Upper (D 9) (R 9) [96,12,33,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8377 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8378 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 152 273 482 450 450 450), lower := (rows 97 14 37 152 273 32 64 128 256), losses := [] }

theorem u8378 : Upper (D 9) (R 9) [96,12,33,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8378 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8379 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 152 274 481 449 449 449), lower := (rows 97 14 37 152 274 32 64 128 256), losses := [] }

theorem u8379 : Upper (D 9) (R 9) [96,12,33,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8379 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8380 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 152 336 419 451 387 387), lower := (rows 97 14 37 152 336 32 64 128 256), losses := [] }

theorem u8380 : Upper (D 9) (R 9) [96,12,33,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8380 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8381 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 200 145 306 338 402 274), lower := (rows 97 14 37 200 145 32 64 128 256), losses := [] }

theorem u8381 : Upper (D 9) (R 9) [96,12,33,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8381 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8382 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 200 146 305 337 401 273), lower := (rows 97 14 37 200 146 32 64 128 256), losses := [] }

theorem u8382 : Upper (D 9) (R 9) [96,12,33,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8382 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8383 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 200 273 434 466 402 402), lower := (rows 97 14 37 200 273 32 64 128 256), losses := [] }

theorem u8383 : Upper (D 9) (R 9) [96,12,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8383 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8384 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 200 274 433 465 401 401), lower := (rows 97 14 37 200 274 32 64 128 256), losses := [] }

theorem u8384 : Upper (D 9) (R 9) [96,12,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8384 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8385 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 200 400 307 339 403 275), lower := (rows 97 14 37 200 400 32 64 128 256), losses := [] }

theorem u8385 : Upper (D 9) (R 9) [96,12,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8385 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8386 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 392 82 433 465 401 401), lower := (rows 97 14 37 392 82 32 64 128 256), losses := [] }

theorem u8386 : Upper (D 9) (R 9) [96,12,33,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8386 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8387 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 392 145 370 338 466 338), lower := (rows 97 14 37 392 145 32 64 128 256), losses := [] }

theorem u8387 : Upper (D 9) (R 9) [96,12,33,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8387 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8388 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 392 146 369 337 465 337), lower := (rows 97 14 37 392 146 32 64 128 256), losses := [] }

theorem u8388 : Upper (D 9) (R 9) [96,12,33,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8388 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8389 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 448 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 97 14 37 392 208 307 339 403 275), lower := (rows 97 14 37 392 208 32 64 128 256), losses := [] }

theorem u8389 : Upper (D 9) (R 9) [96,12,33,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8389 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8390 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,5),(4,6)], upper := (rows 97 14 38 88 145 417 449 385 385), lower := (rows 97 14 38 88 145 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 17 49 0 145 273), good := (rows 433 14 38 446 433 32 0 128 256) }] }

theorem u8390 : Upper (D 9) (R 9) [96,12,34,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8390 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8391 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8391 : Upper (D 9) (R 9) [96,12,34,80,384] 13 := by
  apply FastRouting.sound _ _ [96,12,34,80,384] 13 (by decide) (choices 1) [1,128] r8391 c8391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6011
  · exact u6012

def b8392 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,5)], upper := (rows 97 14 38 137 81 432 464 400 400), lower := (rows 97 14 38 137 81 32 64 128 256), losses := [] }

theorem u8392 : Upper (D 9) (R 9) [96,12,34,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8392 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8393 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 3, region := 16, targets := 320 },{ cop := 4, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,8)], upper := (rows 97 14 38 137 145 368 336 464 336), lower := (rows 97 14 38 137 145 32 64 128 256), losses := [] }

theorem u8393 : Upper (D 9) (R 9) [96,12,34,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8393 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8394 : Route 9 := (fun mask => (mask,id))

def c8394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8394 : Upper (D 9) (R 9) [96,12,34,129,192] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,192] 13 (by decide) (choices 1) [1,16,256] r8394 c8394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6013
  · exact u6014
  · exact u6015

def r8395 : Route 9 := (fun mask => (mask,id))

def c8395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u8395 : Upper (D 9) (R 9) [96,12,34,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,257] 13 (by decide) (choices 1) [16,64,128,256] r8395 c8395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6016
  · exact u6017
  · exact u6018
  · exact u6019

def r8396 : Route 9 := (fun mask => (mask,id))

def c8396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8396 : Upper (D 9) (R 9) [96,12,34,129,320] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,320] 13 (by decide) (choices 1) [1,16,128,256] r8396 c8396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6020
  · exact u6021
  · exact u6022
  · exact u6023

def r8397 : Route 9 := (fun mask => (mask,id))

def c8397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8397 : Upper (D 9) (R 9) [96,12,34,129,384] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129,384] 13 (by decide) (choices 1) [1,16,64,256] r8397 c8397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6024
  · exact u6025
  · exact u6026
  · exact u6027

def b8398 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,5)], upper := (rows 97 14 38 152 81 417 449 385 385), lower := (rows 97 14 38 152 81 32 64 128 256), losses := [] }

theorem u8398 : Upper (D 9) (R 9) [96,12,34,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8398 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8399 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 97 14 38 152 145 353 321 449 321), lower := (rows 97 14 38 152 145 32 64 128 256), losses := [] }

theorem u8399 : Upper (D 9) (R 9) [96,12,34,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8399 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8399
end Delivery.IrregularNine14.P09
